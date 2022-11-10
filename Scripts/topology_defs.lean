import Scripts.topology
import Scripts.finite
--===================================--
------ DEFINICIONES DE TOPOLOGÍA ------
--===================================--

def interior [topological_space α] (s : Set α) : Set α := 
  ⋃₀ (fun o => o ⊆ s ∧ is_open o)

-- El interior de un conjunto es abierto
theorem is_open_interior [T : topological_space α] (s : Set α) : is_open (interior s) := 
  T.is_open_union (fun o => o ⊆ s ∧ is_open o) (fun _ h => h.right)

-- Un punto 'a' es interior a un conjunto 's' si existe un abierto 'g' 
-- que contenga a 'a' contenido en 's'
def interior_point [topological_space α] (a : α) (s : Set α): Prop := 
  ∃ (g : Set α), g ⊆ s ∧ is_open g ∧ a ∈ g

-- Un punto es interior a un conjunto si y solo si está en su interior
theorem interior_point_iff_in_interior [topological_space α] (s : Set α) (a : α) : 
  interior_point a s ↔ a ∈ (interior s) :=
    ⟨fun h => h.elim (fun g ⟨h_subgs,h_openg,h_ag⟩ => Exists.intro g ⟨⟨h_subgs,h_openg⟩,h_ag⟩),
    fun h => h.elim (fun g ⟨⟨h_subgs,h_openg⟩,h_ag⟩ => Exists.intro g ⟨h_subgs,h_openg,h_ag⟩)⟩


----------------------------
--- Sucesión convergente ---
----------------------------

def sequence_limit [topological_space α] (x : Nat → α) (x₀ : α) : Prop :=
  ∀ {g : Set α}, is_open g → x₀ ∈ g → (∃ (n : Nat), ∀ m : Nat, n ≤ m → (x m) ∈ g )

-- El límite de una sucesión convergente contenida en un cerrado
-- pertenece al cerrado
theorem convergent_limit_in_closed [topological_space α] 
        (c : Set α) (h_cc : is_closed c) 
        (x : Nat → α) (h_cx : ∀ n : Nat, (x n) ∈ c) 
        (x₀ : α) (h_xconv : sequence_limit x x₀) : 
        x₀ ∈ c := 
  Classical.byContradiction
    (fun hncx0 => 
      have h_exn : (∃ (n : Nat), ∀ m : Nat, n ≤ m → x m ∈ (-c)) := h_xconv h_cc hncx0
      h_exn.elim (fun n hn =>
        have h_ccxn : x n ∈ (-c) := hn n (Nat.le_refl n)
        have h_cn : x n ∈ c := h_cx n
        (h_ccxn h_cn).elim))

---------------------------
--- Funciones continuas ---
---------------------------

def continuous [topological_space α] [topological_space β] (f : α → β) : Prop := 
  ∀ s : Set β, is_open s → is_open (f⁻¹(s))

structure continuous_functions (α : Type u) (β : Type v) 
  [topological_space α] [topological_space β] where
    function : α → β
    is_continuous : continuous function

notation "C(" α ","  β ")" => continuous_functions α β

theorem continuous_functions_eq
        [topological_space α] [topological_space β] 
        {f g : C(α,β)} : 
        f.function = g.function → f = g :=
  fun heq => show (⟨f.function, f.is_continuous⟩ : C(α,β)) = 
                   ⟨g.function, g.is_continuous⟩
             from by simp [heq]
    

------------------------------------------
--- Topología generada por una subbase ---
------------------------------------------

inductive generated_topology_open (B : Set (Set (α))) : Set α → Prop where
  | basic : (b : Set α) → B b → generated_topology_open B b
  | univ : generated_topology_open B total
  | inter : (b1 b2 : Set α) → generated_topology_open B b1 → 
      generated_topology_open B b2 → generated_topology_open B (b1 ∩ b2)
  | unionF : (Fb : Set (Set α)) → (∀ b, Fb b → generated_topology_open B b) → 
      generated_topology_open B (⋃₀ Fb)

def generated_topology (B : Set (Set α)) : topological_space α :=
  {
    is_open := generated_topology_open B,
    is_open_univ := generated_topology_open.univ,
    is_open_inter := generated_topology_open.inter,
    is_open_union := generated_topology_open.unionF
  }


-------------------------------------
--- Compacidad por recubrimientos ---
-------------------------------------

-- Recubrimientos
def cover (R : Set (Set α)) (s : Set α) : Prop := s ⊆ ⋃₀ R

-- Compactos
def compact [topological_space α] (k : Set α) : Prop :=
  ∀ R, cover R k → (∀ s, R s → is_open s) → 
    (∃ R', R' ⊆ R ∧ is_finite R' ∧  cover R' k)

-- El vacío es compacto
theorem compact_empty [topological_space α] : compact (∅ : Set α) := 
  fun R _ _ =>
    let R' : Set (Set α) := ∅
    Exists.intro R' ⟨empty_subset R, is_finite_empty, empty_subset (⋃₀ R')⟩

-- Los conjuntos unitarios son compactos
theorem compact_singleton [topological_space α] (a : α) : compact { a } :=
  fun R hRcover _ =>
    have huniona : a ∈ ⋃₀ R := hRcover rfl
    huniona.elim (fun s ⟨hRs,hsa⟩ => 
      let R' : Set (Set α) := { s }
      have hsub : R' ⊆ R := (@in_set_iff_singleton_subset _ R s).mp hRs
      have hfinite : is_finite R' := is_finite_singleton s
      have hcover : cover R' { a } := unionF_singleton s ▸ (in_set_iff_singleton_subset.mp hsa)
      Exists.intro R' ⟨hsub, hfinite, hcover⟩)

-- La unión finita de compactos es compacto
theorem compact_union [topological_space α] {k k' : Set α} : compact k → compact k' → compact (k ∪ k') :=
  fun hk hk' => fun R hRcover hRabto =>
    have hRcoverk : cover R k :=  (iff_union_of_subsets.mp hRcover).left 
    have hRcoverk' : cover R k' :=  (iff_union_of_subsets.mp hRcover).right 
    (hk R hRcoverk hRabto).elim (fun Rk ⟨hsubRk, hfinitek, hRkcover⟩ =>
      (hk' R hRcoverk' hRabto).elim (fun Rk' ⟨hsubRk', hfinitek', hRk'cover⟩ =>
        let R' := Rk ∪ Rk'
        have hsub : R' ⊆ R := iff_union_of_subsets.mpr ⟨hsubRk,hsubRk'⟩
        have hfinite : is_finite R' := is_finite_union hfinitek hfinitek'
        have hcoverk : k ⊆ ⋃₀ R' := eq_unionF_of_union ▸ (subset_of_union (⋃₀ Rk') hRkcover).left
        have hcoverk' : k' ⊆ ⋃₀ R' := eq_unionF_of_union ▸ (subset_of_union (⋃₀ Rk) hRk'cover).right
        have hcover : cover R' (k ∪ k') := iff_union_of_subsets.mpr ⟨hcoverk, hcoverk'⟩
        Exists.intro R' ⟨hsub, hfinite, hcover⟩))

-- Los conjuntos finitos son compactos

theorem compact_finite_alt [topological_space α] {s : Set α} : is_finite_alt s → compact s :=
  fun h => 
    match h with
    | is_finite_alt.empty => compact_empty
    | is_finite_alt.singleton _ => compact_singleton _
    | is_finite_alt.union ha hb => compact_union (compact_finite_alt ha) (compact_finite_alt hb)

theorem compact_finite [topological_space α] {s : Set α} : is_finite s → compact s :=
  fun h => compact_finite_alt (is_finite_alt_of_is_finite h)

----------------------------
--- Espacio de Hausdorff ---
----------------------------

def hausdorff_space (α : Type u) [topological_space α] : Prop :=
  ∀ x y : α, x ≠ y → ∃ (u v : Set α), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ disjoint u v


----------------------------------
--- Topología compacto-abierta ---
----------------------------------

def compact_open_subbasis [topological_space α] [topological_space β] : 
  Set (Set C(α,β)) :=
    fun (s : Set C(α,β)) => ∃ (k : Set α) (_ : compact k) (u : Set β) (_ : is_open u),
      (∀ f : C(α,β), f ∈ s →  Im(f.function,k) ⊆ u)

instance compact_open_topology [topological_space α] [topological_space β] : 
  topological_space C(α,β) := generated_topology compact_open_subbasis


-- Si β es un espacio de Hausdorff, entonces C(α,β) con la topología compacto-abierta, también
theorem compacto_abierta_hausdorff [T : topological_space α] [topological_space β] (h : hausdorff_space β) : 
  @hausdorff_space C(α,β) compact_open_topology :=
  let B : Set (Set C(α,β)) := compact_open_subbasis
  (fun f g hneq => 
    have hneqfun : f.function ≠ g.function := contrapositive continuous_functions_eq hneq
    (funext_converse hneqfun).elim
    (fun x hnfxgx => 
      let fx := f.function x
      let gx := g.function x
      (h fx gx hnfxgx).elim
      (fun u hexv => hexv.elim 
      (fun v ⟨hopenu,hopenv,hufx,hvgx,hdisj⟩ =>
        let k := { x }
        have hcompact : compact k := compact_singleton x
        let uf : Set C(α,β) := fun t => Im(t.function, k) ⊆ u
        have huff : f ∈ uf := image_singleton f.function x ▸ in_set_iff_singleton_subset.mp hufx
        let ug : Set C(α,β) := fun t => Im(t.function, k) ⊆ v
        have hugg : g ∈ ug := image_singleton g.function x ▸ in_set_iff_singleton_subset.mp hvgx
        have hBuf : uf ∈ B := ⟨k,hcompact,u,hopenu, fun _ huft => huft⟩
        have hBug : ug ∈ B := ⟨k,hcompact,v,hopenv, fun _ hugt => hugt⟩
        have hopenuf : is_open uf := generated_topology_open.basic uf hBuf
        have hopenug : is_open ug := generated_topology_open.basic ug hBug
        have hdisj2 : disjoint uf ug := 
          fun {t} hinter => 
            have hnotempty := image_of_nonempty t.function (nonempty_singleton x)
            have hempty := empty_of_subset_of_disjoints hdisj hinter.left hinter.right
            hnotempty hempty 
        ⟨uf,ug, hopenuf, hopenug, huff, hugg, hdisj2⟩))))
        