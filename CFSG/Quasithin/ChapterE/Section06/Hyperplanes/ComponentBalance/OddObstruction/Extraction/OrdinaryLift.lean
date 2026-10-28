module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.Preparation
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import Theory.GroupTheory.CharacteristicCentralizerFusion


/-!
# Ordinary component lifting in E.6.19

Let H = C_G(A), R = O(H), and let D be a component of the actual quotient
H/(R A). The canonical residual lift L from `Extraction.Preparation` is an
ordinary component of H. Only the genuine E.6.1 and earlier local hypotheses
are needed; the extra corank and commutator conditions on the detected D are
not needed for this lifting step.

First, L maps to a component of H/R: its map onto D has central kernel,
and a perfect central cover of a quasisimple group is quasisimple. Choose a
nonidentity z in C_V(T). Preparation proves that R is abelian and z inverts
R. Odd-kernel normalizer lifting identifies C_H(z) with C_{H/R}(zR), since
the inverted odd kernel has no z-fixed elements. The former has
characteristic two by the earlier local facts, so the latter cannot contain
a component. Thus zR does not centralize the image of L.

The component commutator dichotomy now puts that image in its commutator
with zR. Inversion is central in Aut(R), so [H,z] centralizes R. Pulling the
image containment back shows L ≤ [L,z]R ≤ C_H(R). The full kernel R A
therefore centralizes L, and the same perfect-central-cover argument proves
that L itself is quasisimple. Subnormality is supplied by Preparation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263); E.6.6(3), pp.246–247; the inversion argument
in 1.1.5(2), pp.501–502 (PDF pp.518–519); and A.3.3(4), pp.42–43.
This supplies the ordinary lifting step, leaving quotient extraction and
final E.6.19 assembly with their existing owners.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
variable {X Y : Type*} [Group X] [Group Y]

-- Restrict the actual homomorphism to a perfect subgroup and its image.
private theorem quasisimple_of_map (f : X →* Y) (L : Subgroup X)
    [Group.IsPerfect L] [IsQuasisimple (L.map f)]
    (hk : f.ker ≤ centralizer (L : Set X)) : IsQuasisimple L := by
  let cover : PerfectCentralCovering.Cover L (L.map f) := {
    toMonoidHom := f.subgroupMap L
    surjective := f.subgroupMap_surjective L
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      have hxk : (x : X) ∈ f.ker := by
        change f (x : X) = 1
        exact congrArg Subtype.val hx
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hk hxk y y.property) }
  exact cover.isQuasisimple

-- The inversion automorphism commutes with every automorphism of the kernel.
private theorem commutator_inverter_centralizes (R : Subgroup X) [R.Normal]
    (z : X) (hinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹) :
    ⁅(⊤ : Subgroup X), zpowers z⁆ ≤ centralizer (R : Set X) := by
  let φ : X →* MulAut R := MulAut.conjNormal
  have hi (r : R) : φ z r = r⁻¹ := Subtype.ext (hinv r r.property)
  have hz : φ z ∈ center (MulAut R) := by
    rw [mem_center_iff]
    intro a
    apply MulEquiv.ext
    intro r
    change a (φ z r) = φ z (a r)
    rw [hi, hi, map_inv]
  have hZ : (zpowers z).map φ ≤ center (MulAut R) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hz
  have hc : (⁅(⊤ : Subgroup X), zpowers z⁆).map φ = ⊥ := by
    rw [map_commutator, commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hZ.trans (center_le_centralizer _)
  have hk := (Subgroup.map_eq_bot_iff _).mp hc
  intro x hx r hr
  have he := DFunLike.congr_fun (MonoidHom.mem_ker.mp (hk hx)) (⟨r, hr⟩ : R)
  have he' : x * r * x⁻¹ = r := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

private theorem odd_inverted_fixed_eq_one [Finite X]
    (R : Subgroup X) (hodd : Nat.Coprime 2 (Nat.card R))
    (z : X) (hinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹)
    {x : X} (hx : x ∈ R) (hfix : x ∈ centralizer ({z} : Set X)) : x = 1 := by
  have he : x = x⁻¹ := by
    calc x = z * x * z⁻¹ := by
           rw [← mem_centralizer_singleton_iff.mp hfix, mul_inv_cancel_right]
         _ = x⁻¹ := hinv x hx
  have hs : (⟨x, hx⟩ : R) ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [pow_two]
    exact (congrArg (fun y => y * x) he).trans (inv_mul_cancel x)
  exact congrArg Subtype.val (hodd.symm.pow_left_bijective.injective
    (hs.trans (one_pow 2).symm))

-- For an involution its cyclic normalizer is its element centralizer.
private theorem quotient_centralizer_image [Finite X]
    (R : Subgroup X) [R.Normal] (hodd : Nat.Coprime 2 (Nat.card R))
    (z : X) (hz : orderOf z = 2) :
    (centralizer ({z} : Set X)).map (QuotientGroup.mk' R) =
      centralizer ({QuotientGroup.mk' R z} : Set (X ⧸ R)) := by
  let q := QuotientGroup.mk' R
  have hqz : orderOf (q z) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, (orderOf_eq_prime_iff.mp hz).1, map_one]
    · intro he
      have hzR : z ∈ R := (QuotientGroup.eq_one_iff z).mp he
      have hs : (⟨z, hzR⟩ : R) ^ 2 = 1 :=
        Subtype.ext (orderOf_eq_prime_iff.mp hz).1
      have hone : z = 1 := congrArg Subtype.val
        (hodd.symm.pow_left_bijective.injective (hs.trans (one_pow 2).symm))
      exact (orderOf_eq_prime_iff.mp hz).2 hone
  let _ : Fact (IsPGroup 2 (zpowers z)) := ⟨IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz, pow_one])⟩
  have he := normalizer_map_quotient_eq_map_normalizer 2 (zpowers z) R inferInstance hodd
  dsimp only at he
  rw [MonoidHom.map_zpowers, normalizer_zpowers_eq_centralizer_of_order_two z hz,
    normalizer_zpowers_eq_centralizer_of_order_two (q z) hqz] at he
  exact he.symm

private theorem quotient_centralizer_injective [Finite X]
    (R : Subgroup X) [R.Normal] (hodd : Nat.Coprime 2 (Nat.card R))
    (z : X) (hinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹) :
    Function.Injective ((QuotientGroup.mk' R).subgroupMap
      (centralizer ({z} : Set X))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  apply odd_inverted_fixed_eq_one R hodd z hinv _ x.property
  exact (QuotientGroup.eq_one_iff (x : X)).mp (congrArg Subtype.val hx)

private theorem quotient_component_not_centralized [Finite X]
    (R : Subgroup X) [R.Normal] (hodd : Nat.Coprime 2 (Nat.card R))
    (z : X) (hz : orderOf z = 2)
    (hinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹)
    (hchar : HasCharacteristicTwo (centralizer ({z} : Set X)))
    {L : Subgroup (X ⧸ R)} (hL : IsComponent (X ⧸ R) L) :
    ¬ L ≤ centralizer ({QuotientGroup.mk' R z} : Set (X ⧸ R)) := by
  let C := centralizer ({z} : Set X)
  let q := QuotientGroup.mk' R
  let e : C ≃* C.map q := MulEquiv.ofBijective (q.subgroupMap C)
    ⟨quotient_centralizer_injective R hodd z hinv, q.subgroupMap_surjective C⟩
  have hchar' : HasCharacteristicTwo (C.map q) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hchar
  intro hLC
  have hL' : IsComponent (C.map q) (L.subgroupOf (C.map q)) :=
    hL.subgroupOf (by rwa [quotient_centralizer_image R hodd z hz])
  let _ : Group.IsNilpotent (pCore 2 (C.map q)) := pCore_isPGroup.isNilpotent
  exact not_isComponent_of_solvable_normal_selfCentralizing
    (pCore 2 (C.map q)) hchar' _ hL'

private theorem centralizes_inverted_odd_kernel [Finite X]
    (R : Subgroup X) [R.Normal] [IsMulCommutative R]
    (hodd : Nat.Coprime 2 (Nat.card R))
    (z : X) (hz : orderOf z = 2)
    (hinv : ∀ r ∈ R, z * r * z⁻¹ = r⁻¹)
    (hchar : HasCharacteristicTwo (centralizer ({z} : Set X)))
    (L : Subgroup X) (hL : IsComponent (X ⧸ R) (L.map (QuotientGroup.mk' R))) :
    L ≤ centralizer (R : Set X) := by
  let q := QuotientGroup.mk' R
  have hne := quotient_component_not_centralized R hodd z hz hinv hchar hL
  have hc : ⁅L.map q, zpowers (q z)⁆ ≠ ⊥ := by
    intro he
    apply hne
    intro l hl
    exact mem_centralizer_singleton_iff.mpr
      (commutator_eq_bot_iff_le_centralizer.mp he hl (q z) (mem_zpowers _)).symm
  have he := (hL.commutator_dichotomy (zpowers (q z))).resolve_left hc
  have hle : L.map q ≤ (⁅L, zpowers z⁆).map q := by
    rw [map_commutator, MonoidHom.map_zpowers, he]
    exact le_iSup_conjugates _ _
  have hpre := map_le_iff_le_comap.mp hle
  rw [comap_map_eq, QuotientGroup.ker_mk'] at hpre
  exact hpre.trans (sup_le
    ((commutator_mono le_top le_rfl).trans (commutator_inverter_centralizes R z hinv))
    R.le_centralizer)

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V A : Subgroup G}

-- Factor the specified quotient map through H/O(H), retaining its central kernel.
private theorem componentLift_modOddCore_isComponent
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D) :
    IsComponent ((centralizer (A : Set G)) ⧸ pPrimeCore 2 (centralizer (A : Set G)))
      ((componentLift A D).map (QuotientGroup.mk' (pPrimeCore 2 (centralizer (A : Set G))))) := by
  let H := centralizer (A : Set G)
  let R := pPrimeCore 2 H
  let q := QuotientGroup.mk' R
  have hRN : R ≤ (quotientKernel A).comap (MonoidHom.id H) := le_sup_left
  let f : H ⧸ R →* CentralizerQuotient A :=
    QuotientGroup.map R (quotientKernel A) (MonoidHom.id H) hRN
  let L := componentLift A D
  have hL := componentLift_isCComponent h earlier hA hD
  let _ := hL.perfect
  let _ := hD.2
  let _ : Group.IsPerfect (L.map q) := Group.IsPerfect.map q
  have hf : f.ker ≤ center (H ⧸ R) := by
    dsimp only [f]
    rw [QuotientGroup.ker_map]
    change (quotientKernel A).map q ≤ center (H ⧸ R)
    have he : (quotientKernel A).map q = (A.subgroupOf H).map q := by
      simp only [quotientKernel, Subgroup.map_sup, q, R, H, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [he]
    rintro x ⟨a, ha, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R y
    simpa only [q, map_mul] using congrArg q (mem_center_iff.mp (subspace_le_center A ha) b)
  have he : (L.map q).map f = D := by
    rw [map_map]
    change L.map (quotientMap A) = D
    exact componentLift_image D
  let _ : IsQuasisimple ((L.map q).map f) := he.symm ▸ hD.2
  exact ⟨hL.subnormal.quotient, quasisimple_of_map f (L.map q)
    (hf.trans (center_le_centralizer _))⟩

/-- The particular residual lift centralizes the actual odd core of C_G(A). -/
theorem componentLift_centralizes_oddCore
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D) :
    componentLift A D ≤ centralizer (pPrimeCore 2 (centralizer (A : Set G)) :
      Set (centralizer (A : Set G))) := by
  let _ := h.elementary
  let H := centralizer (A : Set G)
  let R := pPrimeCore 2 H
  let _ := oddCore_abelian h earlier hA
  obtain ⟨z, hz, hne⟩ := Components.exists_sylow_fixed h
  let zH : H := ⟨z, subspace_le_centralizer hA.1 le_rfl hz.1⟩
  have hzH : orderOf zH = 2 := orderOf_eq_prime
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz.1))
    (fun he => hne (congrArg Subtype.val he))
  have hinv : ∀ r ∈ R, zH * r * zH⁻¹ = r⁻¹ := by
    intro r hr
    apply Subtype.ext
    exact oddCore_inverted h earlier hA hz hne r ⟨r, hr, rfl⟩
  let C := centralizer ({zH} : Set H)
  let B := H ⊓ centralizer ({z} : Set G)
  let e : C ≃* B := {
    toFun := fun x => ⟨x.val.val, x.val.property,
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩,
      mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hB : HasCharacteristicTwo B := by
    have hAC : A ≤ centralizer ({z} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hz.1) a (hA.1 ha))
    have hc := earlier.centralizers A (centralizer ({z} : Set G))
      (h.centralizer_fixedPoint_characteristicTwo earlier hz hne) hAC
      ((IsElementaryAbelian.isPGroup 2 V).to_le hA.1)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (MulEquiv.subgroupCongr (inf_comm (centralizer ({z} : Set G)) H))).mp hc
  exact centralizes_inverted_odd_kernel R pPrimeCore_coprime_card zH hzH hinv
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hB) _
    (componentLift_modOddCore_isComponent h earlier hA hD)

/-- The canonical residual lift of a quotient component is an ordinary component
under the genuine earlier local hypotheses of E.6.19. -/
theorem componentLift_isComponent
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D) :
    IsComponent (centralizer (A : Set G)) (componentLift A D) := by
  let L := componentLift A D
  have hL := componentLift_isCComponent h earlier hA hD
  let _ := hL.perfect
  let _ := hD.2
  let _ : IsQuasisimple (L.map (quotientMap A)) :=
    (componentLift_image D).symm ▸ hD.2
  refine ⟨hL.subnormal, quasisimple_of_map (quotientMap A) L ?_⟩
  rw [quotientMap_ker]
  exact sup_le (le_centralizer_iff.mp (componentLift_centralizes_oddCore h earlier hA hD))
    ((subspace_le_center A).trans (center_le_centralizer _))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
