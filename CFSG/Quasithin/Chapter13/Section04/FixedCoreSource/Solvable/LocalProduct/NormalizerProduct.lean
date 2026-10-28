module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CentralizerProduct
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OmegaLine
public import Theory.GroupTheory.SymmetricThreeNormalSupplementIndex

/-!
# The normalizer supplement and index in the solvable centralizer

The selected S₃ factor moves a normal elementary four-group U. Its fixed
complement excludes the central escaping z from U. The omega-center line
argument therefore puts C_H(U) inside M=N_G(L), yielding the literal product
H=I(H∩M). The original Sylow subgroup and I/O₂(I)≅S₃ give [H:H∩M]=3.

The final application takes R as the actual preimage in T of the action-image
two-core. This proves its normalization by T, derives Thompson noncentrality
from the Baumann bound, selects the S₃ factor with L₁=O^{3′}(C_L(z)), and
combines the quotient, rank-two, product, escape and index conclusions.
No product, index or Thompson-noncentrality premise remains in that endpoint.

This is the two-core-kernel, Baumann-bound branch of 13.4.8. The A₆-block
noncentrality case, larger kernel, residual/order and placement inputs,
the S₃×S₃ quotient and marked chamber remain obligations of
qt-d-1341-solvable-source. Earlier Chapter12/13.3 and 13.4.3–4 source inputs
retain final discharge with qt-d-1341-fixed-core-source.
SourceProduct derives H=L₁IT from the earlier residual statements in this branch.
Source: Aschbacher–Smith 13.4.8, printed pp.904–905, applied to the literal
H=C_G(z), V_H=⟨Ω₁Z(T)^H⟩ of 13.4.9, printed p.906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_thompson_normalizer_product
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hmodel :
      let H := centralizer ({z} : Set G)
      let U := (centralizerOmegaOrbit T z).subgroupOf H
      letI := (centralizerOmegaOrbit_reduced h₀ hz (fun he => hzL (he ▸ one_mem _))).normal
      let q := QuotientGroup.mk' (centralizer (U : Set H))
      Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
        Equiv.Perm (Fin 3))) :
    let H := centralizer ({z} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    H = I ⊔ (H ⊓ normalizer (L : Set G)) := by
  have hz1 : z ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let H := centralizer ({z} : Set G)
  let U := centralizerOmegaOrbit T z
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let W := (⁅U,I⁆ : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hUn : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hIn : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hWU : W ≤ U := le_normalizer_iff_commutator_le_left.mp (hIH.trans hUn)
  have hWT : W ≤ T := hWU.trans ((centralizerOmegaOrbit_le_core h₀ hz hz1).trans
    (hQR.trans hRT))
  have hWn : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅U,I⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅U,I⁆
    have hu : U.map (MulAut.conj t).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (hUn (hTH ht))
    have hi : I.map (MulAut.conj t).toMonoidHom = I :=
      mem_normalizer_iff_map_conj_eq.mp (hIn (hTH ht))
    rw [map_commutator,hu,hi]
  have hUred := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hUred.elementary
  have hUe : IsElementaryAbelian 2 U := by
    have hh : IsElementaryAbelian 2 ((U.subgroupOf H).map H.subtype) :=
      IsElementaryAbelian.map H.subtype
    rwa [map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz)] at hh
  let := hUe
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (inclusion hWU) (inclusion_injective _)
  obtain ⟨hcard,hdis,hprod⟩ := centralizer_thompson_plane_structure h₀ hz hz1 R hRT hQR hJ hsolv hmodel
  have hWne : W ≠ ⊥ := by
    intro he
    change Nat.card W = 4 at hcard
    rw [he,card_bot] at hcard
    omega
  have hzW : z ∉ W := by
    intro hzW
    apply hz1
    apply (disjoint_def.mp hdis) hzW
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hIH ha)
  have hcent := centralizer_plane_le_normalizer_of_omega_index h structural W hWT hWn hWne
    hz hzL hzW hindex
  apply le_antisymm ?_ (sup_le hIH inf_le_left)
  exact hprod.symm.le.trans (sup_le_sup_left (le_inf inf_le_left hcent) I)

/-- The selected symmetric-three normal supplement makes the proper normalizer
intersection have index three in the original involution centralizer. -/
theorem centralizer_thompson_normalizer_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ R)
      (centralizer ({z} : Set G))) ⧸ pCore 2 (conjugateSpanBy (elementaryAbelianMaxJ R)
      (centralizer ({z} : Set G)))) ≃* Equiv.Perm (Fin 3)))
    (hprod : centralizer ({z} : Set G) =
      conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G)) ⊔
        (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    (normalizer (L : Set G)).relIndex (centralizer ({z} : Set G)) = 3 := by
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let N := I.subgroupOf H
  let M := (normalizer (L : Set G)).subgroupOf H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨eI⟩ := hquot
  let eN : N ≃* I := subgroupOfEquivOfLe hIH
  let e : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eI
  apply index_three_of_symmetricThree_normal_supplement N M e (T.subtype hTH)
  · intro t ht
    exact h.source_sylow_normalizes structural ht
  · intro he
    apply hout
    intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ M from he ▸ mem_top _)
  · have hMmap : M.map H.subtype = H ⊓ normalizer (L : Set G) := by
      ext a
      constructor
      · rintro ⟨b,hb,rfl⟩
        exact ⟨b.property,hb⟩
      · rintro ⟨ha,hM⟩
        exact ⟨⟨a,ha⟩,hM,rfl⟩
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,hMmap,
      ← MonoidHom.range_eq_map,H.range_subtype]
    exact hprod.symm

theorem centralizer_single_factor_normalizer_product_of_baumann_bound
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z ∉ centralizer (L : Set G))
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    let H := centralizer ({z} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G) = 2 ∧
      H = I ⊔ (H ⊓ normalizer (L : Set G)) ∧ ¬ I ≤ normalizer (L : Set G) ∧
      (normalizer (L : Set G)).relIndex H = 3 ∧
      (H : Set G) = (I : Set G) * (H ⊓ normalizer (L : Set G) : Set G) := by
  have hz1 : z ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hRT : R ≤ T := by
    rw [hR]
    exact map_subtype_le _
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [hR]
    have hh := (map_mono (show (⊤ : Subgroup T) ≤ normalizer ((pCore 2 K).comap f : Set T)
      from le_normalizer_of_normal)).trans
        (((pCore 2 K).comap f).le_normalizer_map (T : Subgroup G).subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hcore : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · intro a ha
      have hc : (⟨a,hRH ha.1⟩ : H) ∈ centralizer (U : Set H) := by
        intro v hv
        exact Subtype.ext (ha.2 v.val hv)
      exact mem_map_of_mem H.subtype (hkernel ▸ hc)
    · intro a ha
      refine ⟨hQR ha, ?_⟩
      obtain ⟨b,hb,rfl⟩ := ha
      have hc : b ∈ centralizer (U : Set H) := hkernel.symm ▸ hb
      intro v hv
      exact congrArg Subtype.val (hc ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
  have hm := centralizer_thompson_single_factor_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel (firstCentralizerResidual L z) ((firstCentralizerResidual_le L z).trans inf_le_right)
    (firstCentralizerResidual_twoPerfect L z) horder hAN
    (firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree)
  have hp := centralizer_thompson_normalizer_product h₀ h structural hz hzL R hRT hQR hJ hsolv hindex hm
  obtain ⟨hc,hr⟩ := centralizer_thompson_single_factor_data_of_firstResidual
    h₀ hz hz1 R hRT hnR hQR hJ hsolv hkernel horder hthree hAN
  refine ⟨hc,hr,hp,?_,centralizer_thompson_normalizer_index h structural hz R hRT hc hp hout,?_⟩
  · intro hI
    apply hout
    rw [hp]
    exact sup_le hI inf_le_right
  · exact (congrArg (fun A : Subgroup G => (A : Set G)) hp).trans
      (coe_mul_of_right_le_normalizer_left _ _
        (inf_le_left.trans (le_normalizer_conjugateSpanBy _ _)))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
