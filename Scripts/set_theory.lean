import Scripts.logic
--=============================--
------ TΕΟRÍA DE CONJUNTOS ------
--=============================--

--------------------
--- Definiciones ---
--------------------
-- Definición del tipo 'Set'. 'Set α' es el tipo de los conjuntos formados por elementos de α
def Set (α : Type u) := α → Prop


-- Dado un conjunto s : Set α y un término a : α, una prueba de que 'a' pertenece 
-- a 's' es una prueba de 's a'
-- Lean 4 tiene una clase 'Membership α β' que sirve para indicar que hay una noción de pertenencia 
-- de tipo 'α → β → Prop' entre elementos de α y elementos de β.
 
#print Membership

def member (a : α) (s : Set α) : Prop := s a
instance : Membership (α : Type u) (Set α) := Membership.mk (fun a s => s a)

-- Esa instancia nos permite utilizar la notación 'a ∈ s' para 's a'

-- Conjunto vacío
def empty : Set α := fun _ => False

-- Conjunto total (conjunto formado por todos los elementos de α)
def univ : Set α := fun _ => True

-- Para usar la notación ∅ para el conjunto vacío:
instance : EmptyCollection (Set α) := EmptyCollection.mk empty

-- Definición de subconjunto 
def subset (s1 s2 : Set α) : Prop :=
  ∀ {a}, a ∈ s1 → a ∈ s2

-- Introducimos la notación s ⊆ t para subconjunto s t
infix:50 " ⊆ " => subset

-- Unión finita
def union (s t : Set α) : Set α := 
  fun a => a ∈ s ∨ a ∈ t

infixl:65 "∪" => union

-- Intersección finita
def inter (s t : Set α) : Set α :=
  fun a => a ∈ s ∧ a ∈ t 

infixl:65 "∩" => inter

-- Union de familia arbitraria de conjuntos
def unionF (F : Set (Set α)) : Set α := 
  fun a => ∃ s, s ∈ F ∧ a ∈ s

prefix:110 "⋃₀" => unionF

-- Intersección de familia arbitraria de conjuntos 
def interF (F : Set (Set α)) : Set α :=
 fun a => ∀ s, s ∈ F → a ∈ s 

prefix:110 "⋂₀" => interF

-- Conjunto complementario
def compl (s : Set α) : Set α := 
  fun a => ¬ a ∈ s

-- Para la notación '-a' para 'compl a'
instance : Neg (Set α) := Neg.mk compl

-- Familia de complementarios
def complF (F : Set (Set α)) : Set (Set α) := 
  fun s => -s ∈ F

-- Imagen inversa
def preimage (f : α → β) (s : Set β) : Set α := fun a => f a ∈ s
  
notation f "⁻¹(" s ")" => preimage f s

-- Imagen
def image (f : α → β) (s : Set α) : Set β :=
  fun b => ∃ a : α, a ∈ s ∧ f a = b

notation  "Im(" f "," s ")" => image f s

-- Conjuntos disjuntos
def disjoint (s t : Set α) : Prop := (s ∩ t) ⊆ ∅ 

-- Conjunto unitario
def singleton (a : α) : Set α := fun b => b = a

notation "{ " a " }" => singleton a

-------------------
--- PROPIEDADES ---
-------------------

-- Extensionalidad para conjuntos: dos conjuntos son iguales si tienen los mismos elementos
theorem setext {s t : Set α} (h: ∀ {a}, a ∈ s ↔ a ∈ t) : s = t := 
  funext (fun _ => propext h)

theorem obv : (∅ : Set α) = (fun _ => 0 = 1) := 
  setext ⟨fun h => h.elim, fun h => by contradiction⟩

theorem eq_inter_union {s t1 t2 : Set α} : s ∩ (t1 ∪ t2) = (s ∩ t1) ∪ (s ∩ t2) :=
  setext and_or_iff

-- La unión arbitraria de la familia vacía es el conjunto vacío
theorem unionF_empty : ⋃₀ (∅ : Set (Set α)) = (∅ : Set α) := 
  setext ⟨fun h => h.elim (fun _ hand => hand.left), fun h => h.elim⟩


theorem eq_unionF_of_union {A B : Set (Set α)} : ⋃₀ (A ∪ B) = (⋃₀ A) ∪ (⋃₀ B) := 
  setext 
    ⟨fun hex => hex.elim (fun s ⟨hor,hs⟩ => hor.elim (fun hA => Or.inl (Exists.intro s ⟨hA,hs⟩))
                                                     (fun hB => Or.inr (Exists.intro s ⟨hB,hs⟩))),
    fun hor => hor.elim (fun ⟨s,⟨hA,hs⟩⟩ => ⟨s,⟨Or.inl hA,hs⟩⟩)
                        (fun ⟨s,⟨hB,hs⟩⟩ => ⟨s,⟨Or.inr hB,hs⟩⟩)⟩

-----------------------------------
--- Propiedades de subconjuntos ---
-----------------------------------

-- Si dos conjuntos son iguales, entonces están contenidos
-- el uno en el otro
theorem subset_of_eq {s t : Set α} : s = t → subset s t :=
  fun heq => fun hsa => heq ▸ hsa

-- "Ser subconjunto de" es una relación transitiva
theorem subset_trans {s t u : Set α} : s ⊆ t → t ⊆ u → s ⊆ u := 
  fun hst htu => fun hs => htu (hst hs)

-- "Ser subconjunto de" es una relación antisimétrica
theorem eq_of_mutual_subsets {s t : Set α} : s ⊆ t → t ⊆ s → s = t :=
  fun h1 h2 => setext ⟨h1,h2⟩

-- La unión de dos conjuntos 's' y 't' está contenida en un tercer conjunto 'u'
-- si y solo si 's' y 't' están ambos contenidos en 'u'
theorem iff_union_of_subsets {s t u : Set α} : (s ∪ t) ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  ⟨fun h => ⟨fun hsa => h (Or.inl hsa), fun hta => h (Or.inr hta)⟩,
  fun h => fun hunion => hunion.elim (fun hs => h.left hs) (fun ht => h.right ht)⟩

-- Si 's' está contenido en 't', entonces 's' está
-- contenido en la unión de 't' con cualquier otro conjunto.
theorem subset_of_union {s t : Set α} (u : Set α): s ⊆ t → s ⊆ (t ∪ u) ∧ s ⊆ (u ∪ t) :=
  fun h => ⟨fun hs => Or.inl (h hs), fun hs => Or.inr (h hs)⟩

-- Si 's' está contenido en 't', entonces 's' es la intersección de 't' con 's'
theorem eq_subset_inter_subset {s t : Set α} : s ⊆ t → s = s ∩ t := 
  fun hsub => setext ⟨fun hsa => ⟨hsa, hsub hsa⟩, fun hinter => hinter.left⟩

-- Si 's' está contenido en 't1' y en 't2', entonces está contenido en
-- la intersección de 't1' y 't2'
theorem inter_of_double_subset {s t1 t2 : Set α} : s ⊆ t1 → s ⊆ t2 → s ⊆ (t1 ∩ t2) := 
  fun ht1 ht2 => fun hs => ⟨ht1 hs, ht2 hs⟩

--------------------------------------
--- Propiedades del conjunto vacío ---
--------------------------------------

-- El conjunto vacío está contenido en cualquier conjunto
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  fun hfalse => hfalse.elim 

-- Todo subconjunto del vacío es vacío
theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ := 
  fun h => eq_of_mutual_subsets h (empty_subset s)

-- La intersección con el conjunto vacío es el conjunto vacío
theorem eq_inter_empty (s : Set α) : s ∩ ∅ = ∅ :=
  eq_empty_of_subset_empty (fun hinter => hinter.right)

-- Si 's' es subconjunto de conjuntos disjuntos, entonces 's' es vacío
theorem empty_of_subset_of_disjoints {s t1 t2 : Set α} (hdisj : disjoint t1 t2) : s ⊆ t1 → s ⊆ t2 → s = ∅ := 
  fun ht1 ht2 => eq_empty_of_subset_empty (subset_trans (inter_of_double_subset ht1 ht2) hdisj)

-- No existe ningún elemento en el conjunto vacío
theorem notexists_in_empty {α : Type u}: ¬ ∃ a : α, a ∈ (∅ : Set α) := 
  fun hex => hex.elim (fun _ hinempty => hinempty.elim)

-- Si existe un elemento que pertenece a 's', entonces 's' no es el
-- conjunto vacío
theorem nonemptyset_of_exists {s : Set α} : (∃ a, s a) → ¬ s = ∅ :=
  fun hex hempty =>  (notexists_in_empty (hempty ▸ hex)).elim

-- Si no existe ningún elemento que pertenezca a 's', entonces 's'
-- es vacío
theorem emptyset_of_notexists {s : Set α} : (¬ ∃ a, s a) → s = ∅ :=
  fun hnex => (eq_empty_of_subset_empty (fun {a} hsa => hnex ⟨a,hsa⟩))

-- La imagen de un conjunto no vacío es no vacía
theorem image_of_nonempty {s : Set α} (f : α → β) : ¬ s = ∅ → ¬ Im(f,s) = ∅ := 
  fun hnotemptys => fun hemptyfs =>
    have hsubempty : s ⊆ empty := fun {a} hsa => 
      have hfaIm : (f a) ∈ Im(f,s) := Exists.intro a ⟨hsa,rfl⟩
      have hinempty : (f a) ∈ (∅ : Set β) := hemptyfs ▸ hfaIm
      hinempty.elim
    hnotemptys (eq_empty_of_subset_empty hsubempty)


----------------------------------------------
--- Propiedades de los conjuntos unitarios ---
----------------------------------------------

-- Los conjuntos unitarios son no vacíos
theorem nonempty_singleton (a : α) : ¬ singleton a = empty := nonemptyset_of_exists ⟨a,rfl⟩

-- La intersección con un conjunto unitario es o bien el vacío, 
-- o bien el propio conjunto unitario
theorem empty_or_singleton_eq_inter_singleton {s : Set α} {a : α} : 
  empty = (s ∩ { a }) ∨ { a } = (s ∩ { a }) := 
  (Classical.em (s a)).elim
  (fun hsa => 
    Or.inr (setext ⟨fun heqab => ⟨heqab ▸ hsa, heqab⟩, fun hinter => hinter.right⟩))
  (fun hnsa =>
    Or.inl (setext ⟨fun hfalse => hfalse.elim, fun hinter => (hnsa (hinter.right ▸ hinter.left)).elim⟩))

-- La unión de la familia formada por un solo conjunto 's' es igual a 's'
theorem unionF_singleton (s : Set α) : ⋃₀ { s } = s := 
  setext ⟨fun hunion => hunion.elim (fun _ ⟨hsinglF,hta⟩ => hsinglF ▸ hta),
                     fun hsa => Exists.intro s ⟨rfl,hsa⟩⟩

-- La imagen de un conjunto unitario { x } es el conjunto unitario formado
-- por la imagen de 'x'
theorem image_singleton (f : α → β) (a : α) :  Im(f,{ a }) = { f a } := 
  setext (Iff.intro 
    (fun himb => himb.elim (fun _ ⟨hsingaa',heqfa'b⟩ => hsingaa' ▸ heqfa'b.symm))
    (fun hsingfab => Exists.intro a ⟨rfl,hsingfab.symm⟩))

-- Un elemento pertenece a un cierto conjunto si y solo si el conjunto
-- unitario formado por ese elemento está contenido en el conjunto
theorem in_set_iff_singleton_subset {s : Set α} {a : α} : a ∈ s ↔ { a } ⊆ s :=
  Iff.intro
  (fun hsa => fun hbsingl => hbsingl ▸ hsa)
  (fun hsub => hsub rfl)

--------------------------------------
--- Propiedades del complementario ---
--------------------------------------

-- El complementario del vacio es el total
theorem eq_compl_empty :  -(∅ : Set α) = (univ : Set α) := 
  setext notfalse_iff_true

-- El complementario del total es el vacío
theorem eq_compl_univ :  -univ = (∅ : Set α) := 
  setext nottrue_iff_false

-- Propiedad involutiva del complementario
theorem compl_compl_eq {α : Type u} {s : Set α} :  -(-s) = s := 
  setext iff_not_not

-- Complementario de la instersección
theorem compl_inter_eq_union_compl {s t : Set α} : - (s ∩ t) = (-s) ∪ (-t) :=
  setext or_not_iff_not_and

-- Familia de complementarios
theorem complF_of_F {F : Set (Set α)} {s : Set α} : s ∈ F → (-s) ∈ complF F  :=
  fun h : F s =>  
    have h_compl_compl : (-(-s)) ∈ F := compl_compl_eq ▸ h
    h_compl_compl

-- Propiedad involutiva del complementario para familias
theorem complF_complF_eq (F : Set (Set α)) : complF (complF F) = F :=
  have h : ∀ s, s ∈ complF (complF F) ↔ s ∈ F := 
    fun s => 
    ⟨ fun hccs : complF (complF F) s => 
        have h_compl_compl_s : F (- (-s)) := hccs
        show F s from @compl_compl_eq α s ▸ h_compl_compl_s,
      fun h_s : F s => 
        have h_ccF_cc_s : complF (complF F) (compl (compl s)) := complF_of_F  (complF_of_F  h_s)
        @compl_compl_eq α s ▸ h_ccF_cc_s
    ⟩
  setext @h

-- Lema
theorem forall_comp {p : Set α → Prop} {F : Set (Set α)} : (∀ s, s ∈ F → p (-s)) → ∀ s, s ∈ (complF F) → p s :=
  fun h s h_cF_s => @compl_compl_eq α s ▸ h (-s) h_cF_s

-- El complementario de la union de una familia de conjuntos
-- es la intersección de la familia de los complementarios
theorem compl_unionF {F : Set (Set α)} : - (⋃₀ F) = ⋂₀ (complF F) :=
  have h : ∀ a,  a ∈ - (unionF F) ↔ a ∈ ⋂₀ (complF F) := 
    fun a =>
      ⟨fun h_compl_union : a ∈ - (⋃₀ F) => 
        forall_comp (fun s => implies_of_not_and (forall_of_not_exists h_compl_union s)), 
       fun h_inter_compl : a ∈ ⋂₀ (complF F) =>
          fun hunion : a ∈ (⋃₀ F) =>
            hunion.elim 
            (fun s hFssa =>  
              have hcsa : a ∈ (- s) := h_inter_compl (- s) (complF_of_F hFssa.left)
              hcsa hFssa.right)
      ⟩
  setext @h