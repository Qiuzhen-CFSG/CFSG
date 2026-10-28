module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatible

/-!
# Image-eight selection relative to the original quadratic parabolic

The critical transposition lies in the original radical when the first edge
is aligned with the base edge. In its Sylow coordinates, the permutation
(1 4)(3 5) identifies the canonical image-eight transporter with the rotation
of the three original duads. Choosing the transposition conjugator relative
to these duads makes the same transporter normalize the original full-cube
preimage. Every earlier generation equation and the selected-pair common
fixed subgroup are retained.

The original and selected duad matchings form a connected six-cycle, for
both orientations of the paired choice. Their common deleted-module fixed
space is zero. The full-seed displacement coordinates from `EightCompatible`
then give the corresponding original/selected common-fixer identities on
the whole actual seed, preserving both moved covers and all central
attachments. No assertion about arbitrary existential witnesses is used.

The private import intentionally reuses the earlier canonical certificate
and full-seed coordinate argument. Quotient selection and graph transport
are separate lemmas so each elaborates within the default heartbeat limit.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(b),(d), printed pp.917--918; the original-parabolic choice and
common-fixer identities are used in (5.12), printed pp.924--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatibleOriginal
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer hiding r t k
open SectionFive.EightGenerating EightCompatible

private def crossConjugator (i : Fin 3) (ε : Fin 2) : S :=
  BinaryFlags.pairRotation ^ i.val * (Equiv.swap 1 4 * Equiv.swap 3 5) *
    (if ε = 0 then 1 else r⁻¹)

private theorem four_generators_cross_deleted_fixed (m : Fin 2) (i : Fin 3) (ε : Fin 2) (H : Subgroup S)
    (hz : z ∈ H) (hy : y m ∈ H)
    (hzr : (MulAut.conj (crossConjugator i ε)) z ∈ H)
    (hyr : (MulAut.conj (crossConjugator i ε)) (y m) ∈ H) :
    fixedSpace (deletedRepresentation (Fin 6)) H = ⊥ := by
  apply bot_unique
  intro v hv
  obtain ⟨w,rfl⟩ := (constants (Fin 6)).mkQ_surjective v
  have hz' : representation (Fin 6) z w = w :=
    (deleted_fixed_iff_of_fixed_point z w 4 (by decide +kernel)).mp (hv ⟨z,hz⟩)
  have hy' : representation (Fin 6) (y m) w = w :=
    (deleted_fixed_iff_of_fixed_point (y m) w 2 (by fin_cases m <;> decide +kernel)).mp (hv ⟨y m,hy⟩)
  have hzr' : representation (Fin 6) ((MulAut.conj (crossConjugator i ε)) z) w = w :=
    (deleted_fixed_iff_of_fixed_point _ w ((crossConjugator i ε) 4) (by fin_cases i <;> fin_cases ε <;> decide +kernel)).mp (hv ⟨_,hzr⟩)
  have hyr' : representation (Fin 6) ((MulAut.conj (crossConjugator i ε)) (y m)) w = w :=
    (deleted_fixed_iff_of_fixed_point _ w ((crossConjugator i ε) 2) (by fin_cases m <;> fin_cases i <;> fin_cases ε <;> decide +kernel)).mp (hv ⟨_,hyr⟩)
  have cert : ∀ (m : Fin 2) (i : Fin 3) (ε : Fin 2) (w : Full (Fin 6)),
      representation (Fin 6) z w = w → representation (Fin 6) (y m) w = w →
      representation (Fin 6) ((MulAut.conj (crossConjugator i ε)) z) w = w →
      representation (Fin 6) ((MulAut.conj (crossConjugator i ε)) (y m)) w = w →
      ∀ i, w i = w 0 := by
    intro m i ε
    fin_cases m <;> fin_cases i <;> fin_cases ε <;> decide +kernel
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((mem_constants_iff w).mpr ⟨w 0,cert m i ε w hz' hy' hzr' hyr'⟩)

private theorem canonical_cross_deleted_fixed (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hne : ¬ IsElementaryAbelian 2 E)
    (hy : ∃ w ∈ E ⊓ D 6, w (4 : Fin 6) ≠ 4) (i : Fin 3) (ε : Fin 2) :
    let J := E ⊓ D 6
    fixedSpace (deletedRepresentation (Fin 6))
      (J ⊔ J.map (MulAut.conj (crossConjugator i ε)).toMonoidHom) = ⊥ := by
  let J := E ⊓ D 6
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨j₀,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hz : z ∈ J := by
    have he := (NonsylowImage.sylow_square_certificate j₀).resolve_left hsq
    change (sylowWords j₀)^2=z at he
    exact ⟨he ▸ E.pow_mem hx 2,(mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨3,by decide +kernel⟩⟩
  obtain ⟨w,hw,hw4⟩ := hy
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hw.2
  obtain ⟨m,hm⟩ : ∃ m : Fin 2, y m ∈ J := by
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) ≠ 4 →
        ∃ m : Fin 2, y m = dWords j ∨ y m = z*dWords j := by decide +kernel
    obtain ⟨m,he | he⟩ := cert j hw4
    · exact ⟨m,he ▸ hw⟩
    · exact ⟨m,he ▸ J.mul_mem hz hw⟩
  exact four_generators_cross_deleted_fixed m i ε _ (mem_sup_left hz) (mem_sup_left hm)
    (mem_sup_right (mem_map_of_mem _ hz)) (mem_sup_right (mem_map_of_mem _ hm))

private theorem conj_conj_transport {H : Type*} [Group H] (a b c : H) :
    (MulAut.conj a) ((MulAut.conj b) c) =
      (MulAut.conj ((MulAut.conj a) b)) ((MulAut.conj a) c) := by
  change a*(b*c*b⁻¹)*a⁻¹ = (a*b*a⁻¹)*(a*c*a⁻¹)*(a*b*a⁻¹)⁻¹
  group

private theorem inverse_conjugate_mul {H : Type*} [Group H] (a b : H) :
    a*b⁻¹ = ((MulAut.conj a) b)⁻¹*a := by
  change a*b⁻¹ = (a*b*a⁻¹)⁻¹*a
  group

private theorem normalized_original_movers (E J : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hEcard : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hJ : J = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
 :
    let f := (MulAut.conj u⁻¹).toMonoidHom
    E.map f ≤ sylowCarrier ∧ ¬ IsElementaryAbelian 2 (E.map f) ∧
      J.map f = E.map f ⊓ D 6 ∧ Nat.card (E.map f) = 8 ∧
      ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (A : Subgroup S) : (A.map (MulAut.conj u).toMonoidHom).map f = A := by
    rw [conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have hJF : J.map f = E.map f ⊓ D 6 := by
    rw [hJ,map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
  obtain ⟨m,r₀,hr⟩ : ∃ m : Fin 2, ∃ r₀ : S,
      J = (EightSelection.model m).map (MulAut.conj r₀).toMonoidHom := by
    rcases hmodel with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨0,r,hr⟩
    · exact ⟨1,r,hr⟩
  have hmove : ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
    rw [←hJF,hr,conjugate_twice]
    exact EightStrictShift.model_moves m (u⁻¹*r₀) 4
  have hcard : Nat.card (E.map f) = 8 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hEcard]
  exact ⟨hE,hn,hJF,hcard,hmove⟩

private theorem relative_swap_conjugator (u v : S) (hv : v.IsSwap)
    (hvS : v ∈ sylowCarrier.map (MulAut.conj u).toMonoidHom) :
    ∃ i : Fin 3,
      (MulAut.conj (u*BinaryFlags.pairRotation^i.val*(Equiv.swap 1 4*Equiv.swap 3 5))) t = v := by
  obtain ⟨v₀,hv₀,hve⟩ := hvS
  obtain ⟨j,hj⟩ := (mem_sylowCarrier_iff _).mp hv₀
  have hvs : (sylowWords j).cycleType = {2} := by
    have hh := Equiv.Perm.isSwap_iff_cycleType.mp hv
    rw [←hve] at hh
    change (u*v₀*u⁻¹).cycleType = {2} at hh
    rw [Equiv.Perm.cycleType_conj] at hh
    simpa only [hj] using hh
  let q : S := Equiv.swap 1 4 * Equiv.swap 3 5
  have cert : ∀ j : Fin 16, (sylowWords j).cycleType = {2} →
      ∃ i : Fin 3, (MulAut.conj (BinaryFlags.pairRotation ^ i.val * q)) t = sylowWords j := by
    decide +kernel
  obtain ⟨i,hi⟩ := cert j hvs
  refine ⟨i,?_⟩
  change (MulAut.conj u) ((MulAut.conj (BinaryFlags.pairRotation ^ i.val * q)) t) = v
  rw [hi,hj]
  exact hve

private theorem compatible_pair_preserves_original_cube (E J : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hEcard : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hJ : J = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
    (v : S) (hv : v.IsSwap) (hvE : v ∈ E) :
    ∃ w x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      let J₁ := J.map (MulAut.conj w).toMonoidHom
      let E₁ := E.map (MulAut.conj w).toMonoidHom
      J₁ ⊔ zpowers v ⊔ zpowers ((MulAut.conj x) v) = ⊤ ∧
      x⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom ∧
      E₁ ⊔ zpowers v = ⊤ ∧ E₁ ⊔ zpowers ((MulAut.conj x) v) = ⊤ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6)) (J ⊔ J₁) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        (J ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) = ⊥ := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  obtain ⟨hE,hn,hJF,hcard,hmove⟩ :=
    normalized_original_movers E J u hES hEcard hne hJ hmodel
  obtain ⟨hgen,hpair,hleft,hright⟩ := canonical_pair (E.map f) hE hcard hn hmove
  have hfixed := canonical_deleted_fixed (E.map f) hE hn hmove
  rw [←hJF] at hgen hpair hfixed
  obtain ⟨i,hi⟩ := relative_swap_conjugator u v hv (hES hvE)
  let q : S := Equiv.swap 1 4 * Equiv.swap 3 5
  let c₀ : S := u * BinaryFlags.pairRotation ^ i.val
  let k₀ : S := c₀ * q
  have hk : (MulAut.conj k₀).toMonoidHom t = v := hi
  have hcD : (D 6).map (MulAut.conj c₀).toMonoidHom =
      (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [show c₀=u*BinaryFlags.pairRotation^i.val from rfl,←conjugate_twice]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D 6 : Set S)).pow_mem CubeSmallSeeds.rotation_normalizes i.val)
  let x := (MulAut.conj k₀) r
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) k₀
  have hxD : x ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) := by
    have hq : (MulAut.conj q) r = BinaryFlags.pairRotation := by decide +kernel
    have hxe : x = (MulAut.conj c₀) BinaryFlags.pairRotation := by
      change (MulAut.conj c₀) ((MulAut.conj q) r) = _
      rw [hq]
    rw [hxe,←hcD]
    exact le_normalizer_map (MulAut.conj c₀).toMonoidHom
      (mem_map_of_mem _ CubeSmallSeeds.rotation_normalizes)
  have ht : (MulAut.conj k₀).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) v := by
    rw [←hk]
    exact conj_conj_transport k₀ r t
  have hJx : ((J.map f).map (MulAut.conj r⁻¹).toMonoidHom).map (MulAut.conj k₀).toMonoidHom =
      ((J.map f).map (MulAut.conj k₀).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [conjugate_twice (J.map f),conjugate_twice (J.map f)]
    have he : k₀*r⁻¹=x⁻¹*k₀ := inverse_conjugate_mul k₀ r
    rw [he]
  have hJu : (J.map f).map (MulAut.conj u).toMonoidHom = J := by
    rw [conjugate_twice,mul_inv_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hk0 : u * crossConjugator i 0 = k₀ := by
    simp only [crossConjugator,ite_true,mul_one,k₀,c₀,q,mul_assoc]
  have hk1 : u * crossConjugator i 1 = k₀*r⁻¹ := by
    simp only [crossConjugator,show (1 : Fin 2) ≠ 0 from by decide,ite_false,k₀,c₀,q,mul_assoc]
  have hcross0 := canonical_cross_deleted_fixed (E.map f) hE hn hmove i 0
  have hcross1 := canonical_cross_deleted_fixed (E.map f) hE hn hmove i 1
  rw [←hJF] at hcross0 hcross1
  refine ⟨k₀*u⁻¹,x,hx,((MulAut.conj k₀).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel)),hxD,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := mem_map_of_mem (MulAut.conj k₀).toMonoidHom hpair
    rw [Subgroup.map_sup,hJx] at hh
    have hri : (MulAut.conj k₀).toMonoidHom r⁻¹ = x⁻¹ := (MulAut.conj k₀).map_inv r
    simpa only [hri,f,conjugate_twice] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hleft
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hright
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh

  · have hh := deleted_fixed_bot_conjugate _ hfixed k₀
    rw [Subgroup.map_sup,hJx] at hh
    simpa only [f,conjugate_twice] using hh

  · have hh := deleted_fixed_bot_conjugate _ hcross0 u
    rw [Subgroup.map_sup,hJu,conjugate_twice,hk0] at hh
    simpa only [f,conjugate_twice] using hh
  · have hh := deleted_fixed_bot_conjugate _ hcross1 u
    rw [Subgroup.map_sup,hJu,conjugate_twice,hk1,
      ←conjugate_twice (J.map f) r⁻¹ k₀,hJx] at hh
    simpa only [f,conjugate_twice] using hh

private theorem compatible_lifts_preserves_original_cube {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (E J C A : Subgroup H)
    (hC : C.map π = alternatingGroup (Fin 6)) (hkJ : π.ker ≤ J)
    (hJE : J ≤ E) (u : S)
    (hES : E.map π ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hE : Nat.card (E.map π) = 8) (hne : ¬ IsElementaryAbelian 2 (E.map π))
    (hJimage : J.map π = E.map π ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo (J.map π) plus ∨ IsConjugateTo (J.map π) (evenPart 6))
    (a : S) (ha : a ∈ A.map π) (hswap : a.IsSwap) (haE : a ∈ E.map π) :
    ∃ g y : H, y ∈ C ∧ y^3 ∈ π.ker ∧
      π y ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      J₁ ⊔ A ⊔ A₁ = ⊤ ∧ y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A₁ = ⊤ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6)) ((J ⊔ J₁).map π) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        ((J ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π) = ⊥ := by
  obtain ⟨v,b',hb,hbo,hbD,hgen,hpair,hleft,hright,hfixed,hcross0,hcross1⟩ :=
    compatible_pair_preserves_original_cube (E.map π) (J.map π) u hES hE hne hJimage hmodel a hswap haE
  obtain ⟨g,hg⟩ := hs v
  have hbL : b' ∈ C.map π := hC.symm ▸ hb
  obtain ⟨y,hy,hyb⟩ := hbL
  let J₁ := J.map (MulAut.conj g).toMonoidHom
  let E₁ := E.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hJ : J₁.map π = (J.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hEE : E₁.map π = (E.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hker : π.ker.map (MulAut.conj g).toMonoidHom = π.ker :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hkJ₁ : π.ker ≤ J₁ := by rw [←hker]; exact map_mono hkJ
  have hA₁ : A₁.map π = (A.map π).map (MulAut.conj b').toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hyb]
  have htop : J₁ ⊔ A ⊔ A₁ = ⊤ := by
    apply map_injective_of_ker_le π (hkJ₁.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hJ,hA₁,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem (MulAut.conj b').toMonoidHom ha))
  have hyP : y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom := by
    have hh : y⁻¹ ∈ ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π).comap π := by
      change π (y⁻¹) ∈ (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π
      rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
      exact hpair
    rwa [comap_map_eq,sup_eq_left.mpr (hkJ₁.trans le_sup_left)] at hh
  have hkE₁ : π.ker ≤ E₁ := hkJ₁.trans (map_mono hJE)
  have lift_gen (D : Subgroup H) (w : S) (hw : w ∈ D.map π)
      (hgen : (E.map π).map (MulAut.conj v).toMonoidHom ⊔ zpowers w = ⊤) :
      E₁ ⊔ D = ⊤ := by
    apply map_injective_of_ker_le π (hkE₁.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEE,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup_left (zpowers_le.mpr hw) _
  refine ⟨g,y,hy,?_,hyb.symm ▸ hbD,htop,hyP,lift_gen A a ha hleft,lift_gen A₁ ((MulAut.conj b') a) ?_ hright,?_,?_,?_⟩
  · rw [MonoidHom.mem_ker,map_pow,hyb]
    simpa only [hbo] using pow_orderOf_eq_one b'
  · rw [hA₁]
    exact mem_map_of_mem _ ha

  · rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
    exact hfixed

  · rw [Subgroup.map_sup,hJ]
    exact hcross0
  · rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
    exact hcross1


universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem centralizer_sup_eq {H : Type*} [Group H] (P R : Subgroup H) :
    centralizer ((P ⊔ R : Subgroup H) : Set H) =
      centralizer (P : Set H) ⊓ centralizer (R : Set H) := by
  apply le_antisymm
  · intro v hv
    exact ⟨fun j hj => hv j ((show P ≤ P ⊔ R from le_sup_left) hj),
      fun j hj => hv j ((show R ≤ P ⊔ R from le_sup_right) hj)⟩
  · intro v hv
    have hvfix : P ⊔ R ≤ centralizer ({v} : Set H) :=
      sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (hv.1 j hj))
        (fun j hj => mem_centralizer_singleton_iff.mpr (hv.2 j hj))
    exact fun j hj => mem_centralizer_singleton_iff.mp (hvfix hj)

private theorem graph_common_fixed_of_deleted
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (P R : Subgroup d.overgroup)
    (hfixed : fixedSpace (deletedRepresentation (Fin 6)) ((P ⊔ R).map s.projection) = ⊥) :
    (Z d.radical (alpha d.radical) ⊓
      centralizer (P.map (embedM d.radical) : Set (FreeAmalgam d.radical))) ⊓
      centralizer (R.map (embedM d.radical) : Set (FreeAmalgam d.radical)) =
      Z d.radical (alpha d.radical) ⊓
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hmZ : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hfix := full_seed_fixed_of_image_deleted s hc p hsmall (P ⊔ R) hfixed
  have hh := congrArg (Subgroup.map (embedM d.radical)) hfix
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  rw [←map_inf_centralizer_of_injective _ (embedM_injective d.radical) (radiusSeed d) (P ⊔ R),
    ←map_inf_centralizer_of_injective _ (embedM_injective d.radical) (radiusSeed d)
      (⊤ : Subgroup d.overgroup),hmZ,Subgroup.map_sup,
    ←MonoidHom.range_eq_map,hrange] at hh
  rwa [centralizer_sup_eq,←inf_assoc] at hh

private theorem original_cube_source_selection_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    let A := (Z d.radical z).comap (embedM d.radical)
    ∃ u : S,
      (normalizer (d.radical : Set d.overgroup)).map s.projection =
        sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      J₀.map s.projection = d.radical.map s.projection ⊓
        (D 6).map (MulAut.conj u).toMonoidHom ∧
    ∃ g y : d.overgroup, y ∈ replacementComponent d ∧ y^3 ∈ s.projection.ker ∧
      s.projection y ∈ normalizer ((D 6).map (MulAut.conj u).toMonoidHom : Set S) ∧
      let J₁ := J₀.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      J₁ ⊔ A ⊔ A₁ = ⊤ ∧ y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom ∧
      d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      d.radical.map (MulAut.conj g).toMonoidHom ⊔ A₁ = ⊤ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map s.projection) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6)) ((J₀ ⊔ J₁).map s.projection) = ⊥ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        ((J₀ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map s.projection) = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJimage,_,_,_,_⟩ := EightMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb
  have hE : Nat.card (d.radical.map s.projection) = 8 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hcard
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hne
  have hmodel' : IsConjugateTo (J₀.map s.projection) plus ∨
      IsConjugateTo (J₀.map s.projection) (evenPart 6) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  let A := (Z d.radical z).comap (embedM d.radical)
  have hAe : A ≤ d.radical := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [←Q_beta]
    apply (map_comap_le _ _).trans
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant z p.end_color]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    have hp := replacementDistance_pos h d
    change p.walk.length-1 < replacementDistance h d
    omega
  refine ⟨u,hN,hJimage,?_⟩
  exact compatible_lifts_preserves_original_cube s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image hkJ
    (sSup_le fun _ hB => hB.1.1) u ((map_mono d.radical.le_normalizer).trans_eq hN)
    hE hne' hJimage hmodel' a ha hswap (map_mono hAe ha)

include e hz hn in
/-- An aligned critical path admits one paired selection preserving the original
quadratic cube, all endpoint generation equations, and all three common-fixer
identities for the original and paired selected movers on the full seed. -/
theorem paired_generating_original_cube_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    ∃ u : S,
      (normalizer (d.radical : Set d.overgroup)).map s.projection =
        sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      J₀.map s.projection = d.radical.map s.projection ⊓
        (D 6).map (MulAut.conj u).toMonoidHom ∧
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        x ∈ normalizer ((((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection).map
          (embedM d.radical) : Set (FreeAmalgam d.radical)) ∧
        let t := act d.radical g (beta d.radical)
        let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
        let Jb := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical)
        Adjacent d.radical (alpha d.radical) t ∧
          J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          x ∈ J ⊔ J.map (MulAut.conj x).toMonoidHom ∧
          Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
            Z d.radical (alpha d.radical) ⊓
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
          (Z d.radical (alpha d.radical) ⊓ centralizer (Jb : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J : Set (FreeAmalgam d.radical)) =
            Z d.radical (alpha d.radical) ⊓
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
          (Z d.radical (alpha d.radical) ⊓ centralizer (Jb : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
            Z d.radical (alpha d.radical) ⊓
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let A := (Z d.radical z).comap (embedM d.radical)
  obtain ⟨u,hN,hJimage,g,y,hy,hy3,hyD,htop,hpair,hleft,hright,hfixed,hcross0,hcross1⟩ :=
    original_cube_source_selection_knownSimple hne hcard hb hmodel p hsmall hfirst
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,hU,hQ,
      SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  let Jb := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical)
  have hJbm : J₀.map (embedM d.radical) = Jb := by
    change (SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (embedM d.radical) = Jb
    rw [SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←Q_beta]
  have hJxm : (J₁.map (MulAut.conj y⁻¹).toMonoidHom).map (embedM d.radical) =
      J.map (MulAut.conj x).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,map_inv,hJm]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical z :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x z) := by
    rw [SylowCompatible.image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  change y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom at hpair
  have hyN : y ∈ normalizer (((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection : Set d.overgroup) :=
    le_normalizer_comap _ hyD
  have hxN : x ∈ normalizer ((((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection).map
      (embedM d.radical) : Set (FreeAmalgam d.radical)) := by
    change embedM d.radical y⁻¹ ∈ _
    exact le_normalizer_map (embedM d.radical)
      (mem_map_of_mem _ ((normalizer _).inv_mem hyN))
  refine ⟨u,hN,hJimage,f,hf,x,hxL,?_,hxN,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · have hh := mem_map_of_mem (embedM d.radical) hpair
    rwa [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,
      map_inv,hJm] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hleft
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hright
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := graph_common_fixed_of_deleted s hc p hsmall
      J₁ (J₁.map (MulAut.conj y⁻¹).toMonoidHom) hfixed
    rwa [hJm,hJxm] at hh
  · have hh := graph_common_fixed_of_deleted s hc p hsmall J₀ J₁ hcross0
    rwa [hJbm,hJm] at hh
  · have hh := graph_common_fixed_of_deleted s hc p hsmall
      J₀ (J₁.map (MulAut.conj y⁻¹).toMonoidHom) hcross1
    rwa [hJbm,hJxm] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatibleOriginal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
