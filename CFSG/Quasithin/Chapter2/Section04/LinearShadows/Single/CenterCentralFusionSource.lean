module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFusionAlignmentSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterElementaryProductSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFusionEndgameSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterCommutatorCardSource

/-!
# Excluding central outside involutions in the centerless branch

Suppose an element a of T centralizes the distinguished Z and lies in a
conjugate Zᵍ, while a lies outside R. The elementary product V=ZZᵍ has
maximum elementary order. The displacement subgroup K=[R,a] normalizes
V and spans V from Zᵍ. Its order and intersection with V give |KV|=|R|.
Aligning V with U while preserving Z places KV in a conjugate of the
literal Sylow subgroup R of N(U) ∩ C(Z). The TI conjugate-span argument
and weak closure of the elementary Thompson subgroup then force a into R.

Both exported statements use only the original single-block hypotheses;
all elementary, action, cardinality, Sylow, and span premises are discharged.

Source: Aschbacher–Smith, original 2.4.21, middle paragraph of printed p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The central outside-involution branch in the original centerless fusion proof. -/
theorem source_centerless_central_conjugate_exclusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype)=⊥)
    (a g : G) (haT : a∈T)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (ha : a∈(distinguishedZ d).conjBy g)
    (haC : a∈centralizer (distinguishedZ d : Set G)) : False := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let Z := distinguishedZ d
  let E := Z.conjBy g
  let V := Z ⊔ E
  let K := ⁅R,zpowers a⁆
  let W := K ⊔ V
  have hZ := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hZ.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha
  have ha1 : a≠1 := fun he => haR (he ▸ R.one_mem)
  have haS : a∉S := by
    intro h
    apply haR
    exact (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique).le ⟨h,haC⟩
  have heZ : Z=R⊓centralizer (R : Set G) := distinguishedZ_of_centerless d hz
  have haC' : a∈centralizer ((R⊓centralizer (R : Set G) : Subgroup G) : Set G) := by
    rw [←heZ];exact haC
  have hfix := source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hunique a haT haS ha2 haC'
  have hZK : Z≤K := heZ.symm ▸ hfix.2.le
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTN := (d.lemma_2_4_8_1 hG T hST hsingle hL').2.2
  have hKR : K≤R := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (hTN haT))
  have hRC : R≤centralizer (Z : Set G) := le_centralizer_iff.mp (hZ.2.2.1.trans inf_le_right)
  have hprod := source_centerless_centralizing_elementary_product d hG T hST hsingle hL hM hTM hunique hz a g haT haR ha2 ha haC
  have hV : IsElementaryAbelian 2 V := hprod.1
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card V=Nat.card U := hprod.2.1
  have hVR : V⊓R=Z := hprod.2.2.1
  have hVm : V∈Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
    refine ⟨le_top,hV,?_⟩
    intro A _ hA
    rw [hcV]
    exact (source_module_maximum_elementary d hG T hST hsingle hL hM hTM hunique).2.2 A le_top hA
  have hTI := source_distinguished_TI d hG T hST hsingle hL hM hTM hunique
  have hKV : K≤normalizer (V : Set G) := hTI.normalizes_product_of_point_orbit g a K ha ha1 hVm
    (hKR.trans hRC) (by
      intro k hk
      obtain ⟨z,hz,he⟩ := source_outside_involution_coset_stable d hG T hST hsingle hL hM hTM hunique a haT haS ha2 k hk
      have hzZ : z∈Z := heZ.symm ▸ hz
      rw [he]
      exact V.mul_mem (mem_sup_right ha) (mem_sup_left hzZ))
  have hspan : V=conjugateSpanBy E K :=
    ChapterI.Section06To08.product_eq_conjugate_span_of_central_translates Z E K a ha hKV (by
      intro z hzZ
      exact (source_centerless_outside_involution_fusion d hG T hST hsingle hL hM hTM hunique hz a haT haS ha2 haC').1 z (heZ ▸ hzZ))
  have hKVint : V⊓K=Z := by
    apply le_antisymm
    · exact (inf_le_inf_left V hKR).trans hVR.le
    · exact le_inf le_sup_left hZK
  have hcK : Nat.card K=Nat.card Z^2 := by
    rw [heZ]
    exact source_centerless_outside_commutator_card d hG T hST hsingle hL hM hTM hunique hz a haT haS ha2 haC'
  have hcR : Nat.card R=Nat.card Z^3 := by
    rw [heZ]
    exact source_centerless_sylow_card d hG T hST hsingle hL hM hTM hunique hz
  have hcV' : Nat.card V=Nat.card Z^2 := by
    rw [hcV,heZ]
    exact source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hz
  have hcW : Nat.card W=Nat.card R := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes V K hKV
    rw [hKVint,hcV',hcK,sup_comm V K] at hh
    have hp : 0<Nat.card Z := Nat.card_pos
    rw [hcR]
    change Nat.card (K⊔V : Subgroup G)=Nat.card Z^3
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      Nat.card Z * Nat.card (K⊔V : Subgroup G) = Nat.card Z^2 * Nat.card Z^2 := hh.symm
      _ = Nat.card Z * Nat.card Z^3 := by ring
  have hRT : R≤T := (show R≤S from sSup_le fun _ hA=>hA.1).trans hST.le
  have hW : IsPGroup 2 W := (T.isPGroup'.to_le (hKR.trans hRT)).to_sup_of_normal_right' hV.isPGroup hKV
  have hWN : W≤normalizer (V : Set G) := sup_le hKV V.le_normalizer
  have hVC : V≤centralizer (Z : Set G) := by
    have hh : V≤centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact hh.trans (centralizer_le (show Z≤V from le_sup_left))
  have hWC : W≤centralizer (Z : Set G) := sup_le (hKR.trans hRC) hVC
  have haE := ha
  obtain ⟨z,hzZ,hzg⟩ := haE
  have hz1 : z≠1 := by intro he;apply ha1;rw [←hzg,he,map_one]
  obtain ⟨h,hh⟩ := source_centerless_normalizing_product_conjugate d hG T hST hsingle hL hM hTM hunique hz V W hV hcV le_sup_left z hzZ hz1 hW hWN hWC hcW
  exact source_centerless_conjugate_product_exclusion d hG T hST hsingle hL hM hTM hunique hz a g h haT haR ha V hV hcV hspan hh

/-- A T-element fused into Z and centralizing Z belongs to the original R. -/
theorem source_centerless_central_fusion_contained
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype)=⊥)
    (a z : G) (haT : a∈T) (hzZ : z∈distinguishedZ d)
    (hfused : IsConj a z) (haC : a∈centralizer (distinguishedZ d : Set G)) :
    a∈Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  by_contra haR
  obtain ⟨g,hg⟩ := isConj_iff.mp hfused.symm
  exact source_centerless_central_conjugate_exclusion d hG T hST hsingle hL hM hTM hunique hz a g haT haR ⟨z,hzZ,hg⟩ haC

end CFSG.Quasithin.Chapter2.LinearShadows.Single
