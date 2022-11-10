import Scripts.set_theory
--===================--
------ TOPOLOGÍA ------
--===================--

-- Un espacio topológico sobre un tipo α viene dado por un predicado 'is_open' sobre los conjuntos de
-- elementos de α junto con las pruebas de que ese predicado cumple los axiomas de la topología
structure topological_space (α : Type u) where
  is_open : Set α → Prop
  is_open_univ : is_open univ
  is_open_inter : ∀ (s t : Set α), is_open s → is_open t → is_open (s ∩ t) 
  is_open_union : ∀ (F : Set (Set α)), (∀ s, s ∈ F → is_open s) → is_open (⋃₀ F)


--Dos espacios tienen la misma topología si tienen los mismos abiertos
theorem topological_space_eq : ∀ T T' : topological_space α, T.is_open = T'.is_open → T = T' :=
fun ⟨p, _, _, _⟩ ⟨p', _, _, _⟩ h => by simp [h]

theorem topological_space_eq_iff (T : topological_space α) (T' : topological_space α) : 
  (∀ s, T.is_open s ↔ T'.is_open s) ↔ T = T' := 
    ⟨fun h => topological_space_eq T T' (setext @h),
     fun h _ => h ▸ Iff.rfl⟩

-- Por comodidad
attribute [class] topological_space
def is_open [T : topological_space α] : Set α → Prop := T.is_open

-- El vacío siempre es un abierto
theorem is_open_empty {α : Type u} [T : topological_space α] : is_open (∅ : Set α) :=
  have h : is_open (⋃₀ (∅ : Set (Set α))) := 
     T.is_open_union ∅ (fun _ => fun h => h.elim)
  unionF_empty ▸ h

-- Un conjunto es cerrado si su complementario es abierto
def is_closed [topological_space α] (s : Set α) : Prop := is_open (-s)

-- Una topología también puede definirse dando los cerrados
def topological_space_of_is_closed (is_closed : Set α → Prop) (is_closed_empty : is_closed empty)
  (is_closed_union : ∀ (s t : Set α), is_closed s → is_closed t → is_closed (s ∪ t))
  (is_closed_inter : ∀ (F : Set (Set α)), (∀ s, s ∈ F → is_closed s) → is_closed (⋂₀ F)) : 
  topological_space α := 
  {
    is_open := fun s => is_closed (-s),
    is_open_univ := show is_closed (-univ) from eq_compl_univ ▸ is_closed_empty,
    is_open_inter := fun s t hs ht =>
        show is_closed (-(s ∩ t)) from compl_inter_eq_union_compl ▸ (is_closed_union (-s) (-t) hs ht),
    is_open_union := fun F h_open =>
      have h_closed_cF : ∀ s, s ∈ complF F → is_closed s :=
        fun s (h_cF_s : complF F s ) =>
          have h_ccs : is_closed (-(-s)) := h_open (-s) h_cF_s
          @compl_compl_eq α s ▸ h_ccs
      show is_closed (-(⋃₀ F)) from compl_unionF ▸ (is_closed_inter (complF F) h_closed_cF)
  }