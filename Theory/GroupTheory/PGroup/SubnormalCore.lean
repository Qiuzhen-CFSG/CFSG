module
public import Theory.GroupTheory.PGroup.Subnormal

/-!
# Subnormal monotonicity of the ambient p-core

If A is subnormal in a finite subgroup B, then the ambient image of O_p(A)
is contained in that of O_p(B). The p-core is normal in A, so subnormal
transitivity makes its image subnormal in B. It is a p-group, and the
subnormal p-subgroup theorem therefore puts it in O_p(B).

The proof transports the intrinsic p-core through the equivalence between
A and A viewed inside B, then uses the existing subnormal theorem without
repeating its chain induction. This standard finite-group fact supplies
the core inclusion used in Stellmacher (7.7), journal p. 36;
see `refs/latex/stellmacher-n-group.tex`.
-/

/-- Taking ambient p-cores is monotone along subnormal subgroup inclusions. -/
public theorem pCoreAmbient_mono_of_isSubnormalIn
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ)
    (hAB : A ≤ B) (hsub : (A.subgroupOf B).IsSubnormal) :
    (pCore p A).map A.subtype ≤ (pCore p B).map B.subtype := by
  let Q : Subgroup G := (pCore p A).map A.subtype
  have hQA : Q ≤ A := Subgroup.map_subtype_le _
  have hQp : IsPGroup p Q := (pCore_isPGroup (G := A) (p := p)).map A.subtype
  have hQsub : (Q.subgroupOf B).IsSubnormal := by
    let e := Subgroup.subgroupOfEquivOfLe hAB
    have hn : ((pCore p A).comap e.toMonoidHom).IsSubnormal :=
      (pCore_normal (G := A) (p := p)).isSubnormal.comap e.toMonoidHom
    have h := hn.trans' hsub
    have heq : ((pCore p A).comap e.toMonoidHom).map (A.subgroupOf B).subtype =
        Q.subgroupOf B := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        refine ⟨e.symm a, ?_, ?_⟩
        · change e (e.symm a) ∈ pCore p A
          simpa using ha
        · apply Subtype.ext
          exact hax
    rwa [heq] at h
  exact isPGroup_le_pCoreAmbient_of_isSubnormalIn B Q p (hQA.trans hAB) hQsub hQp
