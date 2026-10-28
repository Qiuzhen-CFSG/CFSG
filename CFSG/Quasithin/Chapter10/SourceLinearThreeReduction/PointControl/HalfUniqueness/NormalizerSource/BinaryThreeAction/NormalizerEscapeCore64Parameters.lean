module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64Frattini
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallInnerQuotientAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCubicBudget
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallDegreeThirtyTwo
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeNaturalCoreExclusion

/-!
# The two retained primes in the original full-core order64 branch

Keep both original parabolics and the original full MS core. Its order64
bounds the actual cubic fixed codimension by16. Two conjugates of that
same cubic plane generate K/O₂(K), so the faithful quotient by all fixed
vectors has degree at most32. The native prime-square calculation leaves
exactly p=11 or13. Their exclusion and the nonabelian full-core branch
remain separate source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- Full original core order64 retains only p=11 or13 in the actual
collapsed normalizer-escape configuration. -/
theorem Data.collapsed_fullCore64_prime (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (hcard : Nat.card ((ChapterC.BinaryMS.commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    p = 11 ∨ p = 13 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let C := quotientImage K P
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  let : IsElementaryAbelian 3 P := hpc.1
  let : IsElementaryAbelian 3 (P.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 K))
  have hep : Nonempty (P ≃* C) := by
    change Nonempty (P ≃* quotientImage K P)
    rw [show K = componentOrbit I (T : Subgroup G) from hK]
    exact ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hC : Nat.card C = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let rF : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card,←Nat.card_eq_fintype_card,hF])
  let r := eF.trans (GorensteinWalter.psl2RingEquiv rF).symm
  let j := e.trans (r.prodCongr r)
  let C' := C.map j.toMonoidHom
  let : IsElementaryAbelian 3 C' := IsElementaryAbelian.map j.toMonoidHom
  have hr : primeRank 3 (PSL(2,ZMod p) × PSL(2,ZMod p)) ≤ 2 := by
    rw [←primeRank_congr 3 j,hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3
      (by decide) (by decide)
  have hthree : IsPGroup 3 C' := IsElementaryAbelian.isPGroup 3 C'
  let : IsCyclic (C'.map (MonoidHom.fst _ _)) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let : IsCyclic (C'.map (MonoidHom.snd _ _)) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  obtain ⟨g,hg⟩ := OddSmallDegree.cubic_plane_sup_conjugate_eq_top p
    (by omega : p ≠ 2) C' ((Nat.card_congr (j.subgroupMap C).toEquiv).symm.trans hC)
  have hgen : C ⊔ C.map (MulAut.conj (j.symm g)).toMonoidHom = ⊤ := by
    apply Subgroup.map_injective (f := j.toMonoidHom) j.injective
    rw [Subgroup.map_sup,map_top_of_surjective _ j.surjective]
    have he : (C.map (MulAut.conj (j.symm g)).toMonoidHom).map j.toMonoidHom =
        C'.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      change C.map _ = (C.map j.toMonoidHom).map _
      rw [Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change j (j.symm g*x*(j.symm g)⁻¹) = g*j x*g⁻¹
      simp only [map_mul,map_inv,j.apply_symm_apply]
    rw [he]
    exact hg
  have hpd : p ∣ Nat.card PSL(2,ZMod p) := by
    rw [GorensteinWalter.psl2_card_formula (ZMod p)
      ⟨p,1,hp,ho,by decide,by simp⟩,Nat.card_zmod]
    have htwo : 2 ∣ p^2-1 := by
      obtain ⟨k,hk⟩ := ho.pow (n := 2)
      exact ⟨k,by omega⟩
    rw [Nat.mul_div_assoc p htwo]
    exact dvd_mul_right p _
  have hdiv : p^2 ∣ Nat.card (XiQuotient K) := by
    rw [Nat.card_congr j.toEquiv,Nat.card_prod,pow_two]
    exact Nat.mul_dvd_mul hpd hpd
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  let : IsElementaryAbelian 2 (CoreFrattiniSection T L H) := isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom (h.coreQuotientFrattiniAction hn)
  obtain ⟨hfaith,hsmall⟩ := h.collapsed_fullCore64_cubicFrattini f hn hs.toLocalInput hpc.2 hc hout hcard
  open Representation.BinaryOffender in
  have hfixedFaith : Function.Injective (fixedQuotient ρ ⊤) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    let x : (⊤ : Subgroup (XiQuotient K)) := ⟨a,mem_top a⟩
    have hx : x ∈ (fixedQuotientRepresentation ρ ⊤).ker :=
      (mem_fixedQuotient_ker_iff ρ ⊤ x).mpr ((quotient_kernel_iff ρ ⊤ a).mp ha)
    have hh := fixedQuotient_ker_le_pCore ρ hfaith ⊤ hx
    have hxcore : a ∈ pCore 2 (XiQuotient K) :=
      (pCore_eq_comap_of_normal 2 (⊤ : Subgroup (XiQuotient K))).le hh
    exact (pCore_quotient_pCore_eq_bot 2).le hxcore
  have h1 : C.map (MulAut.conj (1:XiQuotient K)).toMonoidHom = C := by
    rw [map_one]
    change C.map (MonoidHom.id _) = C
    exact map_id C
  open Representation.BinaryOffender in
  have hbound := fixedCodim_le_card_mul_of_subgroup_conjugates ρ ⊤ C
    (fun b : Bool => if b then j.symm g else 1) (by
      simpa only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true,h1,sup_comm] using hgen.ge)
  simp only [Fintype.card_bool] at hbound
  change Representation.BinaryOffender.fixedCodim ρ C ≤ 16 at hsmall
  apply OddSmallDegree.prime_eq_eleven_or_thirteen_of_square_degree_le_thirtyTwo
    (Representation.BinaryOffender.fixedQuotient ρ ⊤) hfixedFaith hp hmod hdiv
  change Representation.BinaryOffender.fixedCodim ρ ⊤ ≤ 32
  omega

/-- The actual abelian MS branch has full core order64 and retains only
the primes11 and13. The natural8 alternative is excluded on the same witnesses. -/
theorem Data.collapsed_abelian_fullCore_parameters (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal)
    (ha : IsMulCommutative (ChapterC.BinaryMS.commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))))) :
    Nat.card ((ChapterC.BinaryMS.commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64 ∧
      (p = 11 ∨ p = 13) := by
  have hcard := (normalizerEscape_abelian_join_core_eq_or_card D s hout ha).resolve_left
    (h.collapsed_natural_join_core_ne f hn hs hK hp ho hm hmod hc)
  exact ⟨hcard,h.collapsed_fullCore64_prime f hn hs hK hp ho hm hmod hc hout hcard⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
