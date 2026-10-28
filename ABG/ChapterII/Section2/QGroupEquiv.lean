module
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import ABG.ChapterII.Section2.SylowShapeTransport
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Enlarged Q-groups are invariant under group equivalence

A multiplicative equivalence between finite groups preserves the full enlarged
Q-group predicate, even when its source and target have different universes.
The quaternion-overgroup definition uses an overgroup in the ambient universe;
its semidihedral or wreathed presentation makes it finite, so it can be realized
in the target universe without changing its group structure.

Transport the actual Sylow subgroup and normal subgroup through the supplied
equivalence, and the largest quaternion subgroup through the finite overgroup
equivalence. Cardinalities and subgroup correspondence preserve maximality and
uniqueness of that quaternion subgroup. Surjective weak-closure transport and
the center-image identity preserve every weakly closed central subgroup. The
restricted Sylow equivalence carries the normal-subgroup intersection exactly,
so the defining quaternion witness remains linked to the transported normal
subgroup. Its two-power index and exclusion of normal index-two subgroups are
preserved as well; no full Sylow shape is assumed of the ambient group.

This is the isomorphism-invariance of Alperin--Brauer--Gorenstein II.2
Definition 3, used to transport the finite-group statement of II.3 Proposition
3 (article pp24–27) through finite universe reduction. The public theorem
supports the arbitrary-universe semilinear assembly; its helpers are private.
-/

namespace ABG
universe u v

private theorem largest_quaternion_map {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (Y : Subgroup S) (hY : IsLargestQuaternionSubgroup Y) :
    IsLargestQuaternionSubgroup (Y.map e.toMonoidHom) := by
  have hcardY : Nat.card (Y.map e.toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn, ⟨eY⟩⟩ := hY.1
    exact ⟨n, hn, ⟨(e.subgroupMap Y).symm.trans eY⟩⟩
  · intro Z hZ
    let A := Z.comap e.toMonoidHom
    have hAZ : A.map e.toMonoidHom = Z :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective Z
    let eA : A ≃* Z := (e.subgroupMap A).trans (MulEquiv.subgroupCongr hAZ)
    have hAQ : IsGeneralizedQuaternionGroup A := by
      obtain ⟨n, hn, ⟨eZ⟩⟩ := hZ
      exact ⟨n, hn, ⟨eA.trans eZ⟩⟩
    obtain ⟨hle, heq⟩ := hY.2 A hAQ
    have hcardA := Nat.card_congr eA.toEquiv
    refine ⟨by omega, ?_⟩
    intro hc
    have hAY : A = Y := heq (by omega)
    rw [← hAZ, hAY]

private theorem qGroup_transport
    {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (hG : IsQGroup G) : IsQGroup H := by
  obtain ⟨S, iS, hS, R, f, Y, K, hf, hY, hKN, ⟨m, hKi⟩, hKno, hRweak, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hG
  let : Group S := iS
  have hSfinite : Finite S := by
    rcases hS with ⟨n, _, hc, _⟩ | ⟨n, _, hc, _⟩
    · exact Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    · exact Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  let : Finite S := hSfinite
  obtain ⟨T, iT, iTf, ⟨eS⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, v} S
  let : Group T := iT
  let : Fintype T := iTf
  have hT : Stellmacher.IsSemidihedralGroup T ∨ IsWreathedGroup T := by
    rcases hS with hsemi | ⟨n, hw⟩
    · exact Or.inl (semidihedral_equiv eS hsemi)
    · exact Or.inr ⟨n, wreathed_equiv eS hw⟩
  let Rbar : Sylow 2 H := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRbar : (Rbar : Subgroup H) = (R : Subgroup G).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  let er : R ≃* Rbar :=
    (e.subgroupMap (R : Subgroup G)).trans (MulEquiv.subgroupCongr hRbar.symm)
  have her (x : R) : (er x : H) = e x := rfl
  let Kbar := K.map e.toMonoidHom
  have hKbarN : Kbar.Normal := hKN.map e.toMonoidHom e.surjective
  have hKbarI : Kbar.index = 2 ^ m := (K.index_map_equiv e).trans hKi
  let eK : K ≃* Kbar := e.subgroupMap K
  have hKbarNo : HasNoNormalIndexTwoSubgroup Kbar := by
    intro A hAN hAi
    let : A.Normal := hAN
    exact hKno (A.comap eK.toMonoidHom) inferInstance
      ((A.index_comap_of_surjective eK.surjective).trans hAi)
  have hRbarWeak : HasWeaklyClosedCenterSubgroups (Rbar : Subgroup H) := by
    intro Z hZ
    have hcenter : subgroupCenter (Rbar : Subgroup H) =
        (subgroupCenter (R : Subgroup G)).map e.toMonoidHom := by
      rw [hRbar, subgroupCenter_map]
    have h := hRweak.weaklyClosedIn_of_le_map e.toMonoidHom e.surjective Z (hcenter ▸ hZ)
    rwa [← hRbar] at h
  have hinter : (Kbar.comap (Rbar : Subgroup H).subtype).map er.symm.toMonoidHom =
      K.comap (R : Subgroup G).subtype := by
    rw [Subgroup.map_equiv_eq_comap_symm' er.symm]
    ext x
    change (er x : H) ∈ Kbar ↔ (x : G) ∈ K
    rw [her]
    exact SetLike.ext_iff.mp
      (Subgroup.comap_map_eq_self_of_injective e.injective K) (x : G)
  apply isQGroup_iff_quaternionOvergroup.mpr
  refine ⟨T, iT, hT, Rbar, eS.toMonoidHom.comp (f.comp er.symm.toMonoidHom),
    Y.map eS.toMonoidHom, Kbar, eS.injective.comp (hf.comp er.symm.injective),
    largest_quaternion_map eS Y hY, hKbarN, ⟨m, hKbarI⟩, hKbarNo, hRbarWeak, ?_⟩
  rw [← Subgroup.map_map, ← Subgroup.map_map, hinter, hlink]

public theorem isQGroup_iff_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) : IsQGroup G ↔ IsQGroup H :=
  ⟨qGroup_transport e, qGroup_transport e.symm⟩

end ABG
