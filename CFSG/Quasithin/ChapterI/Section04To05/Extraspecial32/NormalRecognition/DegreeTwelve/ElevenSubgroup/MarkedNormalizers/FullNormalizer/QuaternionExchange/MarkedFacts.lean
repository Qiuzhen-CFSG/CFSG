module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.Exchange
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Relative normalizers of the literal marked even fusion subgroup

The marked sign map cuts A(z) into a four-group complementary to ⟨z⟩.
An element of Q_z normalizing that four-group centralizes it: each
commutator lies both in the four-group and in the disjoint central line.
It therefore centralizes A(z), so lies in A(z). The resulting index bound
places its relative normalizer inside the marked transposition centralizer
by comparing their orders, both 48.

For any element of S, its centralizer in S normalizes its canonical fusion
subgroup intersected with the marked A₆. The cardinality transport for the
second centralizer is used after the quaternion exchange.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8, p.41.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.SymmetricSixData

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h} (s : SymmetricSixData h a)

theorem fusionCore_le_S : fusionCore z ≤ s.S := by
  rw [s.generated]
  exact le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem markedAlternating_le : s.markedAlternating ≤ s.S := map_subtype_le _

theorem mem_markedAlternating_iff (x : G) (hx : x ∈ s.S) :
    x ∈ s.markedAlternating ↔ s.equiv ⟨x, hx⟩ ∈ alternatingGroup (Fin 6) := by
  constructor
  · rintro ⟨v, hv, he⟩
    have he' : v = ⟨x, hx⟩ := Subtype.ext he
    subst v
    exact hv
  · intro hxA
    exact ⟨⟨x, hx⟩, hxA, rfl⟩

theorem le_normalizer_markedAlternating : s.S ≤ normalizer (s.markedAlternating : Set G) := by
  let A := (alternatingGroup (Fin 6)).comap s.equiv.toMonoidHom
  intro x hx
  apply A.le_normalizer_map s.S.subtype
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [A.normalizer_eq_top]
  exact mem_top _

private theorem centralizer_normalizes_fusion (x : G) :
    Centralizer x ≤ normalizer (fusionCore x : Set G) := by
  have hcore : Centralizer x ≤ normalizer (coreInG x : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (coreInG_le x)).mp
    rw [coreInG_subgroupOf]
    infer_instance
  apply le_normalizer_closure_iff.mpr
  intro g hg u hu
  exact subset_closure ⟨(mem_normalizer_iff.mp (hcore hg) u).mp hu.1,
    hu.2.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩

theorem centralizer_le_relative_normalizer (v : G) : s.S ⊓ Centralizer v ≤
    Centralizer v ⊓ normalizer (s.evenFusion v : Set G) := by
  intro x hx
  refine ⟨hx.2, ?_⟩
  exact inf_normalizer_le_normalizer_inf
    ⟨centralizer_normalizes_fusion v hx.2, s.le_normalizer_markedAlternating hx.1⟩

theorem z_not_mem_markedAlternating : z ∉ s.markedAlternating := by
  intro hz
  have he := Equiv.Perm.mem_alternatingGroup.mp
    ((s.mem_markedAlternating_iff z s.z_mem).mp hz)
  rw [s.z_swap.sign_eq] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

theorem evenFusion_z_card (d : FusionEightData z) : Nat.card (s.evenFusion z) = 4 := by
  let f : fusionCore z →* ℤˣ := Equiv.Perm.sign.comp
    (s.equiv.toMonoidHom.comp (inclusion s.fusionCore_le_S))
  have hf : Function.Surjective f := by
    intro x
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact ⟨1, f.map_one⟩
    · exact ⟨⟨z, h.involution_mem_fusionCore⟩, s.z_swap.sign_eq⟩
  have hker : f.ker = (s.evenFusion z).subgroupOf (fusionCore z) := by
    ext x
    change Equiv.Perm.sign (s.equiv ⟨x, s.fusionCore_le_S x.property⟩) = 1 ↔
      (x : G) ∈ fusionCore z ⊓ s.markedAlternating
    rw [mem_inf, and_iff_right x.property, s.mem_markedAlternating_iff,
      Equiv.Perm.mem_alternatingGroup]
  have hind : f.ker.index = 2 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  have hc := f.ker.card_mul_index
  rw [hind, d.card, hker, Nat.card_congr
    (subgroupOfEquivOfLe (show s.evenFusion z ≤ fusionCore z from inf_le_left)).toEquiv] at hc
  omega

theorem evenFusion_z_inf_zpowers : s.evenFusion z ⊓ zpowers z = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro x hx
  have hline : x ∈ zpowers z := hx.2
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hline
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hline
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · exact (s.z_not_mem_markedAlternating (by simpa using hx.1.2)).elim

theorem evenFusion_z_sup_zpowers (d : FusionEightData z) :
    s.evenFusion z ⊔ zpowers z = fusionCore z := by
  have hle : s.evenFusion z ⊔ zpowers z ≤ fusionCore z :=
    sup_le inf_le_left (zpowers_le.mpr h.involution_mem_fusionCore)
  have hn : zpowers z ≤ normalizer (s.evenFusion z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact zpowers_le.mpr (centralizer_le (show s.evenFusion z ≤ fusionCore z from inf_le_left)
      (d.centralizer_eq.symm ▸ h.involution_mem_fusionCore))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (s.evenFusion z) (zpowers z) hn
  rw [s.evenFusion_z_card d, Nat.card_zpowers, h.involution,
    s.evenFusion_z_inf_zpowers, card_bot, one_mul] at hc
  exact eq_of_le_of_card_ge hle (by rw [d.card, ← hc])

open scoped commutatorElement in
theorem core_inf_evenFusion_z_normalizer (d : FusionEightData z) :
    coreInG z ⊓ normalizer (s.evenFusion z : Set G) = fusionCore z := by
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  apply le_antisymm
  · intro x hx
    rw [← d.centralizer_eq]
    have hfix : x ∈ centralizer (s.evenFusion z : Set G) := by
      intro u hu
      have hline : ⁅x, u⁆ ∈ zpowers z := by
        rw [← h.coreInG_center_image]
        have hc : ⁅(⟨x, hx.1⟩ : coreInG z), ⟨u, fusionCore_le z hu.1⟩⁆ ∈
            center (coreInG z) :=
          (IsExtraspecial.quotient_elementary_abelian 2 (coreInG z)).commutator_le_center_of_central_quotient
            (commutator_mem_commutator (mem_top _) (mem_top _))
        exact mem_map_of_mem (coreInG z).subtype hc
      have hfour : ⁅x, u⁆ ∈ s.evenFusion z :=
        (s.evenFusion z).mul_mem ((mem_normalizer_iff.mp hx.2 u).mp hu)
          ((s.evenFusion z).inv_mem hu)
      have he : ⁅x, u⁆ = 1 :=
        mem_bot.mp (s.evenFusion_z_inf_zpowers ▸ ⟨hfour, hline⟩)
      exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    have hcomm : fusionCore z ≤ Centralizer x := by
      rw [← s.evenFusion_z_sup_zpowers d]
      refine sup_le ?_ (zpowers_le.mpr ?_)
      · intro u hu
        exact mem_centralizer_singleton_iff.mpr (hfix u hu)
      · exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (coreInG_le z hx.1)).symm
    intro u hu
    exact mem_centralizer_singleton_iff.mp (hcomm hu)
  · intro x hx
    refine ⟨fusionCore_le z hx, centralizer_le_normalizer _ ?_⟩
    apply centralizer_le (show s.evenFusion z ≤ fusionCore z from inf_le_left)
    exact d.centralizer_eq.symm ▸ hx

theorem evenFusion_z_relative_normalizer_card_le (d : FusionEightData z) :
    Nat.card (Centralizer z ⊓ normalizer (s.evenFusion z : Set G) : Subgroup G) ≤ 48 := by
  let N := Centralizer z ⊓ normalizer (s.evenFusion z : Set G)
  have hn : N ≤ normalizer (coreInG z : Set G) := by
    rw [h.normalizer_core]
    exact inf_le_left
  have hi : coreInG z ⊓ N = fusionCore z := by
    rw [← s.core_inf_evenFusion_z_normalizer d]
    exact (inf_assoc _ _ _).symm.trans
      (congrArg (fun Q => Q ⊓ normalizer (s.evenFusion z : Set G))
        (inf_eq_left.mpr (coreInG_le z)))
  have hsup : coreInG z ⊔ N ≤ Centralizer z := sup_le (coreInG_le z) inf_le_left
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (coreInG z) N hn
  rw [h.coreInG_card, hi, d.card] at hc
  have hb := card_le_of_le hsup
  rw [h.centralizer_card] at hb
  change Nat.card N ≤ 48
  omega

theorem card_inf_centralizer (x : G) (hx : x ∈ s.S) :
    Nat.card (s.S ⊓ Centralizer x : Subgroup G) =
      Nat.card (centralizer ({s.equiv ⟨x, hx⟩} : Set (Equiv.Perm (Fin 6)))) := by
  let e := s.equiv.toEquiv.subtypeEquiv
    (p := fun y : s.S => (y : G) ∈ s.S ⊓ Centralizer x)
    (q := fun p => p ∈ centralizer ({s.equiv ⟨x, hx⟩} : Set (Equiv.Perm (Fin 6))))
    (fun y => by
      change ((y : G) ∈ s.S ∧ (y : G) ∈ Centralizer x) ↔ _
      rw [and_iff_right y.property, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      constructor
      · intro hy
        simpa only [map_mul, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using congrArg s.equiv
          (Subtype.ext hy : y * ⟨x, hx⟩ = ⟨x, hx⟩ * y)
      · intro hy
        have he : y * ⟨x, hx⟩ = ⟨x, hx⟩ * y := s.equiv.injective (by
          simpa only [map_mul, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] using hy)
        exact congrArg Subtype.val he)
  exact Nat.card_congr
    ((subgroupOfEquivOfLe (show s.S ⊓ Centralizer x ≤ s.S from inf_le_left)).toEquiv.symm.trans e)

theorem centralizer_z_card : Nat.card (s.S ⊓ Centralizer z : Subgroup G) = 48 := by
  rw [s.card_inf_centralizer z s.z_mem, Equiv.Perm.nat_card_centralizer,
    Equiv.Perm.isSwap_iff_cycleType.mp s.z_swap]
  norm_num

theorem centralizer_triple_card (x : G) (hx : x ∈ s.S)
    (hc : (s.equiv ⟨x, hx⟩).cycleType = {2, 2, 2}) :
    Nat.card (s.S ⊓ Centralizer x : Subgroup G) = 48 := by
  rw [s.card_inf_centralizer x hx, Equiv.Perm.nat_card_centralizer, hc]
  norm_num

theorem centralizer_z_eq_relative_normalizer (d : FusionEightData z) :
    s.S ⊓ Centralizer z = Centralizer z ⊓ normalizer (s.evenFusion z : Set G) := by
  apply eq_of_le_of_card_ge (s.centralizer_le_relative_normalizer z)
  rw [s.centralizer_z_card]
  exact s.evenFusion_z_relative_normalizer_card_le d

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.SymmetricSixData

end
