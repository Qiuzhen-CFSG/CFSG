module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.Arithmetic

/-! Concatenate independently checked row batches without repeating their arithmetic. -/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.AlternatingCertificate

lemma checkProducts_append (ts xs zs xs' zs' : List Nat)
    (h : checkProducts ts xs zs = true) (h' : checkProducts ts xs' zs' = true) :
    checkProducts ts (xs ++ xs') (zs ++ zs') = true := by
  induction xs generalizing zs with
  | nil =>
    cases zs with
    | nil => exact h'
    | cons z zs => simp [checkProducts] at h
  | cons x xs ih =>
    cases zs with
    | nil => simp [checkProducts] at h
    | cons z zs =>
      simp only [checkProducts, Bool.and_eq_true] at h
      simp only [List.cons_append, checkProducts, Bool.and_eq_true]
      exact ⟨h.1, ih zs h.2⟩

lemma checkProducts_flatten (ts : List Nat) (xs zs : List (List Nat))
    (h : List.Forall₂ (fun x z => checkProducts ts x z = true) xs zs) :
    checkProducts ts xs.flatten zs.flatten = true := by
  induction h with
  | nil => rfl
  | cons h ht ih =>
    simp only [List.flatten_cons]
    exact checkProducts_append _ _ _ _ _ h ih

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts.AlternatingCertificate
