module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearLifts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LinearMembership

/-! The actual moved section distinguishes the two linear-three flags.
The intentional private import uses only the record-free intertwiner lemma
`moved_linear_three_flags`. The original normalizer, seed module and maps
remain literal throughout the residual-membership proof. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterB.QuasisimpleSource Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- Both native parabolic residuals are members of the original local family,
after one conjugation of the actual image marking. The action kernel is
proved to be exactly the original two-core. -/
theorem PreparedChosenModule.raw_linear_residual_members
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 K : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (K : Set G)
    let H := K ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ∀ hr : IsPReduced 2 W,
    letI := hr.elementary
    let C := centralizer (W : Set H)
    let qH := QuotientGroup.mk' C
    let I := (K.subgroupOf H).map qH
    let ρ := NormalElementaryQuotient.representation W qH
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (f : K →* I) (ec : (K ⧸ pCore 2 K) →* I),
      (∀ x : K, (f x : H ⧸ C) = qH (inclusion le_sup_left x)) →
      (∀ x : K, ec (QuotientGroup.mk' (pCore 2 K) x) = f x) →
      Function.Surjective f → Function.Surjective ec → ec.ker ≤ center (K ⧸ pCore 2 K) →
    ∀ (J : Subgroup (H ⧸ C)) (_hIJ : I ≤ J)
      (s : MovedSection (ρ.comp J.subtype) (I.subgroupOf J))
      (F : BinaryField) (r : ℕ), 0 < r → 1 < F.degree →
      (Nonempty (ActionEquiv (s.action.comp (I.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r)) ∨
       Nonempty (ActionEquiv (s.space.toRepresentation.comp (I.subgroupOf J).subtype)
        (repeated (linearNatural F 3) r))) →
    ∃ e : I ≃* SL(3,F.Carrier), f.ker = pCore 2 K ∧
      ∀ P ∈ ({pointParabolicSL F.Carrier,lineParabolicSL F.Carrier} : Set (Subgroup SL(3,F.Carrier))),
        let B := (P.comap (e.toMonoidHom.comp f)).map K.subtype
        (solvableResidual B).map B.subtype ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := by
  intro S R H W hr
  let := hr.elementary
  intro C qH I ρ f ec hval hproj hf hec hcentral J hIJ s F r hrpos hn hm
  have he : Nonempty (I ≃* SL(3,F.Carrier)) := by
    rcases hm with hc | hc
    · obtain ⟨c⟩ := hc
      exact ⟨(subgroupOfEquivOfLe hIJ).symm.trans c.groupEquiv⟩
    · obtain ⟨c⟩ := hc
      exact ⟨(subgroupOfEquivOfLe hIJ).symm.trans c.groupEquiv⟩
  obtain ⟨e⟩ := he
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hbij := h.raw_local_linearThree_cover_bijective hG T hZ hZne hK.1 hq hfour
    (e.toMonoidHom.comp ec) (e.surjective.comp hec) (by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact hcentral)
  let eq := MulEquiv.ofBijective (e.toMonoidHom.comp ec) hbij
  have hker : f.ker = pCore 2 K := by
    ext x
    change f x = 1 ↔ x ∈ pCore 2 K
    rw [←hproj x]
    exact (show ec (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔
      QuotientGroup.mk' (pCore 2 K) x = 1 from
      ⟨fun hh => hbij.1 (by
        change e (ec (QuotientGroup.mk' (pCore 2 K) x)) = e (ec 1)
        simp only [hh,map_one]),
        fun hh => hh ▸ ec.map_one⟩).trans (QuotientGroup.eq_one_iff x)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F.Carrier - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hEven : Even (Nat.card F.Carrier) := by
      rw [F.card_eq]
      exact Nat.even_pow.mpr ⟨by decide,by omega⟩
    exact (Nat.Even.sub_odd (by omega) hEven (by decide)).not_two_dvd_nat hd
  let : Fact p.Prime := ⟨hp⟩
  have hnK : S ≤ normalizer (K : Set G) :=
    h.raw_local_normalizes_of_oddRank hG T hZ hZne hK hq hp (hp.odd_of_ne_two hp2) (by
      rw [primeRank_equiv p eq]
      exact Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd)
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q₀ := e.toMonoidHom.comp f
  have hq₀ : Function.Surjective q₀ := e.surjective.comp hf
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(3,F.Carrier)) (Q.mapSurjective hq₀)
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F.Carrier F.degree_pos F.card_eq)
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp f
  have hU : (Q : Subgroup K).map q = unipotentSL F.Carrier := by
    have hh := congrArg (fun U : Sylow 2 SL(3,F.Carrier) => (U : Subgroup SL(3,F.Carrier))) hg
    change ((Q : Subgroup K).map q₀).map (MulAut.conj g).toMonoidHom = unipotentSL F.Carrier at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup K) = (S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show S ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let : (K.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer inf_le_right)
  let : I.Normal := inferInstanceAs ((K.subgroupOf H).map qH).Normal
  have hSH : S ≤ H := by
    have he : R = S := inf_eq_left.mpr hnK
    change S ≤ K ⊔ R
    rw [he]
    exact le_sup_right
  let j : S →* H := inclusion hSH
  let α : S →* MulAut SL(3,F.Carrier) := (MulAut.congr e').toMonoidHom.comp
    (MulAut.conjNormal.comp (qH.comp j))
  have heq (x : S) (k : K) :
      q (K.normalizerMonoidHom (inclusion hnK x) k) = α x (q k) := by
    change e' (f _) = e' ((MulAut.conjNormal (qH (j x))) (e'.symm (e' (f k))))
    rw [e'.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hval]
    change qH _ = qH (j x) * (f k : H ⧸ C) * (qH (j x))⁻¹
    rw [hval,←map_inv,←map_mul,←map_mul]
    rfl
  have hnSK : S ≤ normalizer ((S ⊓ K) : Set G) :=
    (le_inf S.le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
  have hUi (x : S) : (unipotentSL F.Carrier).map (α x).toMonoidHom = unipotentSL F.Carrier := by
    have hh := EquivariantLift.map_invariant K q hnK α heq (D := S ⊓ K) hnSK x
    rw [←hQL,hU] at hh
    exact hh
  have hpair (x : S) :
      (pointParabolicSL F.Carrier).map (α x).toMonoidHom = pointParabolicSL F.Carrier ∧
      (lineParabolicSL F.Carrier).map (α x).toMonoidHom = lineParabolicSL F.Carrier :=
    CaseIComponentData.moved_linear_three_flags ρ I J hIJ s F hrpos hm e' (qH (j x)) (hUi x)
  refine ⟨e',hker,?_⟩
  intro P hP B
  let A := (solvableResidual B).map B.subtype
  have hPi (x : S) : P.map (α x).toMonoidHom = P := by
    rcases hP with rfl | hP
    · exact (hpair x).1
    · have he : P = lineParabolicSL F.Carrier := hP
      subst P
      exact (hpair x).2
  have hnB : S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    obtain ⟨k,hk,rfl⟩ := hb
    let x₀ : S := ⟨x,hx⟩
    refine ⟨K.normalizerMonoidHom (inclusion hnK x₀) k,?_,rfl⟩
    change q (K.normalizerMonoidHom (inclusion hnK x₀) k) ∈ P
    rw [heq]
    exact hPi x₀ ▸ mem_map_of_mem (α x₀).toMonoidHom hk
  have hnA : S ≤ normalizer (A : Set G) :=
    hnB.trans (normalizer_le_normalizer_characteristic_image B (solvableResidual B))
  let : Group.IsPerfect A := Group.IsPerfect.map B.subtype
  have hkq : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,hker]
    exact pCore_isPGroup
  obtain ⟨hfit,⟨er⟩⟩ := RawClassicalResidual.linear_data K q (e'.surjective.comp hf) hkq hfour P hP
  let : IsSimpleGroup SL(2,F.Carrier) := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := er.isSimpleGroup
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (pCore 2 A))
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (A ⧸ pCore 2 A)) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : A.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hb : pCore 2 A = ⊥ := (map_eq_bot_iff_of_injective _ A.subtype_injective).mp hh
    have ht := centralizer_generalizedFitting_le A
    rw [hfit,hb] at ht
    rw [show centralizer ((⊥ : Subgroup A) : Set A) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup A) ≤ center A from bot_le)] at ht
    exact (top_ne_bot : (⊤ : Subgroup A) ≠ ⊥) (bot_unique ht)
  have hAK : A ≤ K := (map_subtype_le _).trans (map_subtype_le _)
  exact ⟨hAK.trans hK.1,
    (Chapter1.mem_LIn_of_normalized_perfect hK.2.2.1 (hAK.trans le_sup_left) hnA hc).2⟩

end CFSG.Quasithin.Chapter15.Section01
