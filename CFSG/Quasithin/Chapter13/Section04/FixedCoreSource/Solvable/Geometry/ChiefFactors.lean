module
public import Theory.Representation.BinaryPermutation.SynthemeCoreChief
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.LineParabolics

/-!
# Three chief factors for the original second-parabolic residual

Let J be the T-normalized inner second parabolic, with its actual image
in the quotient marked as the syntheme stabilizer. Its embedded residual
K=O²(J) maps onto the tetrahedral A₄ with exactly O₂(L)∩K as kernel.
A cubic in K fixes only C_V(L), so its fixed index on the original V is
16. Since V normalizes K, coprime fixed-point lifting preserves this
index on V∩K. The kernel therefore contributes at least two noncentral
binary chief factors; the A₄ quotient contributes a third. The count
holds for every complete chief series of the literal K.

The same marking proves J/O₂(J)≅S₃ and hence JT/O₂(JT)≅S₃. The
embedded two-residual of JT equals K, retaining both inclusion maps.
OriginalChief applies this to the original-R₁ local product and supplies
13.4.7(a) together with the already proved (b–c) clauses. The native
second-parabolic marking remains explicit in this increment; connecting
it to the original notation remains with qt-d-1341-solvable-source.
The 13.4.7 alternatives and final earlier-source discharge remain with
qt-d-1341-fixed-core-source. No chief-count or recognition assumption is used.
Source: Aschbacher–Smith Notation13.2.1 and13.4.9, printed pp.877,906.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Subgroup Theory.GroupTheory
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem syntheme_cubic_fixed
    (D : ChosenModule T L V) (m : CoreMarking D)
    (K : Subgroup G) (hKL : K ≤ L) (f : K →* A)
    (hmark : ∀ k : K, (m.quotient (QuotientGroup.mk' (centralCore L)
      (inclusion hKL k))).val = synthemeHom (f k))
    (a : K) (ha : orderOf (f a) = 3) :
    V ⊓ centralizer ({a.val} : Set G) = V ⊓ centralizer (L : Set G) := by
  apply le_antisymm ?_ (inf_le_inf_left V (centralizer_le (Set.singleton_subset_iff.mpr (hKL a.property))))
  intro v hv
  refine ⟨hv.1,(m.mem_fixed_iff ⟨v,hv.1⟩).mpr ?_⟩
  apply (BinaryPermutation.SynthemeCoreChief.cubic_fixed_iff (f a) ha _).mp
  rw [← hmark a,← m.equivariant (inclusion hKL a)]
  congr 2
  apply Subtype.ext
  change a.val * v * a.val⁻¹ = v
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hv.2).symm

theorem marked_plane_residual_chief_count
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (K : Subgroup G) (hKL : K ≤ L) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (f : K →* A) (hf : Function.Surjective f)
    (hmark : ∀ k : K, (m.quotient (QuotientGroup.mk' (centralCore L)
      (inclusion hKL k))).val = synthemeHom (f k))
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    3 ≤ s.noncentralTwoCount := by
  let Q := L.pCoreIn 2
  have hk : f.ker = Q.subgroupOf K := by
    ext k
    change f k = 1 ↔ k.val ∈ Q
    rw [← synthemeHom_injective.eq_iff, map_one,← hmark k]
    change (m.quotient (QuotientGroup.mk' (centralCore L) (inclusion hKL k))).val =
      (1 : alternatingGroup (Fin 6)).val ↔ _
    rw [Subtype.val_injective.eq_iff,m.quotient.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff,
      centralCore_eq_twoCore_of_ordinary eL]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact (isPGroup_pCoreIn 2 L).comap_subtype
  have hd : 3 ∣ Nat.card K := dvd_trans (b := Nat.card A) (by
    rw [nat_card_alternatingGroup]; norm_num) (card_dvd_of_surjective f hf)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
  let B := zpowers a.val
  have hBK : B ≤ K := zpowers_le.mpr a.property
  have hB : Nat.card B = 3 := by rw [Nat.card_zpowers,K.orderOf_coe,ha]
  have hBi : Nat.card (B.subgroupOf K) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hB
  have hai : orderOf (f a) = 3 := by
    have hc := GLS3.Chapter5.cubic_image_card_of_two_kernel f hp (zpowers a)
      (by rw [Nat.card_zpowers,ha])
    rwa [MonoidHom.map_zpowers,Nat.card_zpowers] at hc
  have hfixed : V ⊓ centralizer (B : Set G) = V ⊓ centralizer (L : Set G) := by
    rw [show centralizer (B : Set G) = centralizer ({a.val} : Set G) by
      dsimp only [B]; rw [zpowers_eq_closure,centralizer_closure]]
    exact syntheme_cubic_fixed D m K hKL f hmark a hai
  have hlen : conjugationCubicLength B V = 2 := by
    have hc : Nat.card ((centralizer (B : Set G)).subgroupOf V) = 2 := by
      rw [← inf_subgroupOf_right,inf_comm (centralizer (B : Set G)),hfixed]
      exact (Nat.card_congr (subgroupOfEquivOfLe (show V ⊓ centralizer (L : Set G) ≤ V
        from inf_le_left)).toEquiv).trans m.card_fixed
    have hm := ((centralizer (B : Set G)).subgroupOf V).card_mul_index
    rw [hc,m.card_module] at hm
    have hi : (centralizer (B : Set G)).relIndex V = 16 := by
      change 2 * (centralizer (B : Set G)).relIndex V = 32 at hm
      omega
    rw [conjugationCubicLength,hi]
    decide
  have hinter := CubicComparison.intersection_length_eq B V K
    (IsPGroup.of_card (n := 1) (by simpa using hB))
    (letI := D.elementary; IsElementaryAbelian.isPGroup 2 V) hBK
    (D.le_sylow.trans hTK) (hKL.trans D.normalizes)
  have hlow : 2 ≤ conjugationCubicLength B (Q ⊓ K) := by
    rw [← hlen,← hinter]
    exact conjugationCubicLength_mono B (inf_le_inf_right K D.le_componentCore)
  have hcount := CubicComparison.alternatingFour_count f hf hp (B.subgroupOf K) hBi s h0 h1
  have he := CubicComparison.length_subgroupOf B (Q ⊓ K) K hBK inf_le_right
  rw [inf_subgroupOf_right,← hk] at he
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Subgroup Theory.GroupTheory
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the tetrahedral quotient of the original embedded two-residual
from the actual second-parabolic image in the chosen component quotient. -/
theorem second_parabolic_residual_action
    (D : ChosenModule T L V) (m : CoreMarking D)
    (J : Subgroup G) (hJL : J ≤ L)
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6)) :
    let K := (pResidual 2 J).map J.subtype
    ∃ f : K →* A, Function.Surjective f ∧
      ∀ k : K, (m.quotient (QuotientGroup.mk' (centralCore L)
        (inclusion ((map_subtype_le _).trans hJL) k))).val = synthemeHom (f k) := by
  let K := (pResidual 2 J).map J.subtype
  let α : L →* S6 := (alternatingGroup (Fin 6)).subtype.comp
    (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))
  have hKL : K ≤ L := (map_subtype_le _).trans hJL
  have hres : K.subgroupOf L =
      (pResidual 2 (J.subgroupOf L)).map (J.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hKL,map_embedded_pResidual,map_subgroupOf_eq_of_le hJL]
  have himageK : (K.subgroupOf L).map α = synthemeHom.range := by
    rw [hres,map_embedded_pResidual]
    rw [himage]
    exact BinaryPermutation.SynthemeCoreChief.even_syntheme_residual
  let β := α.comp (inclusion hKL)
  have hr : β.range = synthemeHom.range := by
    rw [←himageK]
    ext g
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨inclusion hKL k,k.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k.val,hk⟩,rfl⟩
  let e := MonoidHom.ofInjective synthemeHom_injective
  let b : K →* synthemeHom.range := β.codRestrict _ (fun k => hr ▸ ⟨k,rfl⟩)
  have hb : Function.Surjective b := by
    intro a
    have ha : a.val ∈ β.range := hr.symm ▸ a.property
    obtain ⟨k,hk⟩ := ha
    exact ⟨k,Subtype.ext hk⟩
  let f := e.symm.toMonoidHom.comp b
  refine ⟨f,e.symm.surjective.comp hb,?_⟩
  intro k
  exact congrArg Subtype.val (e.apply_symm_apply (b k)).symm

/-- Three noncentral binary chief factors on the literal source second
residual: two from V and one from its tetrahedral quotient. -/
theorem second_parabolic_residual_three_chief_factors
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (s : ChiefSeries ((pResidual 2 J).map J.subtype))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : 3 ≤ s.noncentralTwoCount := by
  obtain ⟨f,hf,hmark⟩ := second_parabolic_residual_action D m J hJL himage
  exact marked_plane_residual_chief_count D m eL _ ((map_subtype_le _).trans hJL)
    (hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J)))
    f hf hmark s h0 h1

/-- Adjoining the original Sylow preserves the literal embedded residual. -/
theorem second_parabolic_full_residual
    (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) :
    (pResidual 2 (J ⊔ (T : Subgroup G) : Subgroup G)).map
      (J ⊔ (T : Subgroup G)).subtype = (pResidual 2 J).map J.subtype := by
  let K := (pResidual 2 J).map J.subtype
  have he : J ⊔ (T : Subgroup G) = K ⊔ (T : Subgroup G) :=
    le_antisymm (sup_le (le_embedded_pResidual_sup_sylow_of_normalizes T J hTJ) le_sup_right)
      (sup_le_sup_right (map_subtype_le _) _)
  rw [he]
  exact embedded_pResidual_join_pGroup K (T : Subgroup G)
    (isPPerfect_embedded_pResidual 2 J) T.isPGroup'
    (hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J)))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Subgroup Theory.GroupTheory
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original inner second parabolic has a symmetric-three core quotient,
through the very same component marking as the five-dimensional module. -/
theorem second_parabolic_core_quotient
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup G) (hJL : J ≤ L)
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6)) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
  let q : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hmem (j : J) : q (inclusion hJL j) ∈ a6SynthemeStabilizer := by
    have hh : (q (inclusion hJL j)).val ∈ synthemeStabilizer ⊓ alternatingGroup (Fin 6) := by
      rw [←himage]
      exact mem_map_of_mem _ j.property
    exact hh.1
  let f : J →* a6SynthemeStabilizer := (q.comp (inclusion hJL)).codRestrict _ hmem
  have hf : Function.Surjective f := by
    intro a
    have hh : a.val.val ∈ synthemeStabilizer ⊓ alternatingGroup (Fin 6) :=
      ⟨a.property,a.val.property⟩
    rw [←himage] at hh
    obtain ⟨l,hl,he⟩ := hh
    exact ⟨⟨l.val,hl⟩,Subtype.ext (Subtype.ext he)⟩
  have hk : f.ker = (centralCore L).comap (inclusion hJL) := by
    ext j
    change (⟨q (inclusion hJL j),_⟩ : a6SynthemeStabilizer) = 1 ↔ _
    rw [Subtype.ext_iff]
    change m.quotient (QuotientGroup.mk' (centralCore L) (inclusion hJL j)) = 1 ↔ _
    rw [m.quotient.map_eq_one_iff,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    rfl
  have hp : IsPGroup 2 f.ker := by
    rw [hk,centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  exact ⟨(f.pCoreQuotientEquiv hf hp).trans a6SynthemeCoreQuotientEquiv⟩

/-- The full original second parabolic retains this S₃ quotient after adjoining T. -/
theorem second_parabolic_full_core_quotient
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6)) :
    let B := J ⊔ (T : Subgroup G)
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) := by
  let B := J ⊔ (T : Subgroup G)
  let N := J.subgroupOf B
  let S := (T : Subgroup G).subgroupOf B
  have hJB : J ≤ B := le_sup_left
  have hTB : (T : Subgroup G) ≤ B := le_sup_right
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le J.le_normalizer hTJ)
  obtain ⟨eJ⟩ := second_parabolic_core_quotient D m eL J hJL himage
  let eN := subgroupOfEquivOfLe hJB
  have hgen : N ⊔ S = ⊤ := by
    rw [←subgroupOf_sup hJB hTB]
    exact subgroupOf_self B
  exact NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement N S
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eJ)
    T.isPGroup'.comap_subtype hgen

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
