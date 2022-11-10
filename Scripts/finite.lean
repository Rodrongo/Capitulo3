import Scripts.set_theory
--===========================--
------ CONJUNTOS FINITOS ------
--===========================--

structure finite {α : Type u} {β : Type v} [Membership α β] (b : β) where
  list : List α
  all_in_list : ∀ {a}, a ∈ b → a ∈ list  -- a ∈ list es equivalente a List.Mem 
                                        --a list (hay una instancia de Membership 
                                        -- para listas con mem = List.Mem)


inductive is_finite {α : Type u} {β : Type v} [Membership α β] (b : β) : Prop where
  | intro : finite b → is_finite b


----------------------------------------
--- Propiedades de conjuntos finitos ---
----------------------------------------

-- El conjunto vacío es finito
theorem is_finite_empty {α : Type u} : is_finite (∅ : Set α) := 
  let list := []
  have all_in_list : ∀ {a}, a ∈ (∅ : Set α) → a ∈ list := fun h => h.elim
  is_finite.intro ⟨list, all_in_list⟩

-- Los conjuntos unitatios son finitos
theorem is_finite_singleton (a : α) : is_finite { a } :=
  let list := [a]
  have obv : a ∈ list := List.Mem.head  []
  have all_in_list : ∀ {b}, b ∈ ({ a } : Set α) → b ∈ list := fun h => h ▸ obv
  is_finite.intro ⟨list, all_in_list⟩

-- La unión de conjuntos finitos es finito
theorem is_finite_union {s t : Set α} : is_finite s → is_finite t → is_finite (s ∪ t) :=
  fun (is_finite.intro ⟨list_s, all_in_list_s⟩) (is_finite.intro ⟨list_t, all_in_list_t⟩) =>
    let list := list_s ++ list_t 
    have all_in_list : ∀ {a}, a ∈ (s ∪ t) → a ∈ list := fun hunion => 
      hunion.elim (fun hsa => List.mem_append_of_mem_left list_t (all_in_list_s hsa))
                  (fun hta => List.mem_append_of_mem_right list_s (all_in_list_t hta))
    is_finite.intro ⟨list, all_in_list⟩

#check @List.mem_append_of_mem_right -- ∀ {α : Type u_1} {b : α} {bs : List α} (as : List α), b ∈ bs → b ∈ as ++ bs


--------------------------------------------------
--- Conjuntos finitos (definición alternativa) ---
--------------------------------------------------
inductive is_finite_alt : Set α → Prop where
  | empty : is_finite_alt ∅
  | singleton : ∀ a, is_finite_alt { a }
  | union : ∀ {s t}, is_finite_alt s → is_finite_alt t → is_finite_alt (s ∪ t)

-----------------------------------------------------------------
--- Propiedades de conjuntos finitos (definición alternativa) ---
-----------------------------------------------------------------

theorem is_finite_inter_with_finite  {s t : Set α} : is_finite_alt t → is_finite_alt (s ∩ t) := 
  fun hfinitet =>
    match hfinitet with 
    | is_finite_alt.empty => 
      (eq_inter_empty s).symm ▸ is_finite_alt.empty
    | is_finite_alt.singleton a =>
      empty_or_singleton_eq_inter_singleton.elim
      (fun h_empty => h_empty ▸ is_finite_alt.empty)
      (fun h_single => h_single ▸ is_finite_alt.singleton a)
    | is_finite_alt.union ht1 ht2 =>
      eq_inter_union ▸ is_finite_alt.union (is_finite_inter_with_finite ht1) (is_finite_inter_with_finite ht2)

theorem subset_of_finite {s t : Set α} : s ⊆ t → is_finite_alt t → is_finite_alt s :=
  fun hsub hfinitet => eq_subset_inter_subset hsub ▸ is_finite_inter_with_finite hfinitet

-- EQUIVALENCIA DE AMBAS DEFINICIONES

-- La siguiete implicación es directa a partir de las propiedades probadas para 'is_finite'
theorem is_finite_of_is_finite_alt {s : Set α} : is_finite_alt s → is_finite s :=
  fun h =>
    match h with 
    | is_finite_alt.empty => is_finite_empty
    | is_finite_alt.singleton _ => is_finite_singleton _
    | is_finite_alt.union ht1 ht2 => is_finite_union (is_finite_of_is_finite_alt ht1) (is_finite_of_is_finite_alt ht2)

-- La implicación contraria requiere de algunos lemas previos

theorem lemma1 {s : Set α} (h : ∀ {a}, a ∈ s → a ∈ []) : s = ∅ := 
  eq_empty_of_subset_empty (fun hsa => have contr := h hsa; by contradiction)

theorem lemma2 {a : α} {as : List α} : 
  (fun b => b ∈ (a::as)) = { a } ∪ (fun b => b ∈ as) :=
    setext 
      ⟨fun hbinlist => 
      match hbinlist with 
      | List.Mem.head as =>
        Or.inl rfl
      | List.Mem.tail a h_b_in_as => 
        Or.inr h_b_in_as, 
      fun hunionb =>
        hunionb.elim
        (fun hsingle =>
          hsingle ▸ List.Mem.head as)
        (fun hbintail =>
          List.Mem.tail a hbintail)⟩

theorem lemma3 : ∀ as : List α, is_finite_alt (fun a => a ∈ as) 
  | [] =>
    have hempty : (fun a => a ∈ []) = (∅ : Set α) := lemma1 id
    hempty ▸ is_finite_alt.empty
  | a::as => 
    have div : (fun b => b ∈ (a::as)) = { a } ∪ (fun b => b ∈ as) := lemma2
    div ▸ is_finite_alt.union (is_finite_alt.singleton a) (lemma3 as)


theorem is_finite_alt_of_is_finite {s : Set α} : is_finite s → is_finite_alt s :=
  fun (is_finite.intro ⟨list, all_in_list⟩) =>
  -- 'list' es una lista con los elementos de 's'
  -- 'all_in_list' es la prueba de que todos los 
  -- elementos de 's' están en 'list'
    let finiteSet : Set α := (fun b => b ∈ list)
    have hsub : s ⊆ finiteSet := all_in_list
    have hfin : is_finite_alt finiteSet := lemma3 list
    subset_of_finite hsub hfin

theorem is_finite_iff_is_finite_alt {s : Set α} : is_finite s ↔ is_finite_alt s :=
  ⟨is_finite_alt_of_is_finite,is_finite_of_is_finite_alt⟩