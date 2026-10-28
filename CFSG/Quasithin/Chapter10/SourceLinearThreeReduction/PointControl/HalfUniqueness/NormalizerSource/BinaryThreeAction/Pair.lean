module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.FixedLayer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Model
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The selected binary-three pair before point control

The zero-kernel natural marking, full/local equality and original exchanger
construct coordinates on the two actual moved factors. Their generation and
disjointness follow from the original pair action. No survivor, point-centralizer
bound or half-Sylow normalizer is needed. These coordinates are the input to the
wreath action and the two parabolics in source 10.2.5.

The coordinate proofs adapt the later replacement modules Geometry/Pair,
Geometry/Escape/Coordinates and Parabolic/Natural/Coordinates to precisely
these earlier hypotheses, without changing their public interfaces.
Source: Aschbacher--Smith 10.1.1(3), 10.2.4--5, pp.741,747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Only the already selected natural action and original pair data. The
constructor below derives generation and vanishing of the full fixed part. -/
structure NaturalData (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  exchange : G
  exchange_mem : exchange ∈ T
  exchange_moves : exchange ∉ normalizer (L : Set G)
  full_eq_local : D.fullModule = D.moduleSubgroup
  generated : D.fullModule = ⁅D.fullModule,L⁆ ⊔
    (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom
  crossed : (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom ≤
    centralizer (L : Set G)
  quotient : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  natural : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    ((Representation.specialLinearNatural 3).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
  fixed_zero : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥

/-- Construct the pair on the specified exchanger from the exact zero-kernel
branch of the selected module, without any later source conclusions. -/
theorem exists_naturalData (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ∃ s : NaturalData D, s.exchange = t := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hgen : D.fullModule = ⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
    obtain ⟨s,_,_,_,hV,hpair⟩ := source_nonnormal_fullModule_pair D hn
    have hne : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≠ ⁅D.fullModule,L⁆ := by
      intro he
      have hc : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) := he ▸ hcross
      have hz : ⁅⁅D.fullModule,L⁆,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
      exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans hz)
    have he := (hpair t (le_normalizer_componentOrbit L T ht)).resolve_left hne
    exact hV.trans (congrArg (fun X : Subgroup G => ⁅D.fullModule,L⁆ ⊔ X) he.symm)
  have hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
    rw [Selection.BinaryThree.fixed_layer_eq_moved_kernels D ht htn hcross,
      hzero,Subgroup.map_bot,sup_bot_eq]
  exact ⟨⟨t,ht,htn,hfull,hgen,hcross,e,c,hz⟩,rfl⟩

variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L} (s : NaturalData D)

include s

/-- The specified exchange witnesses the original nonnormal case. -/
theorem selected_nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
  fun h => s.exchange_moves (h s.exchange_mem)

/-- The first moved factor lies in the original full module. -/
theorem selected_moved_le : ⁅D.fullModule,L⁆ ≤ D.fullModule := by
  exact le_sup_left.trans_eq s.generated.symm

/-- The exchanged moved factor lies in the same full module. -/
theorem selected_partner_le :
    (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤ D.fullModule := by
  exact le_sup_right.trans_eq s.generated.symm

/-- The whole original maximal local group permutes the two moved factors. -/
theorem selected_moved_pair (g : G) (hg : g ∈ D.maximalLocal) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have hV (m : G) (hm : m ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  rw [map_commutator, hV g hg, map_commutator,
    hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem)]
  rcases source_nonnormal_maximal_pair D (selected_nonnormal s)
      s.exchange_mem s.exchange_moves g hg with h | h
  · exact Or.inl (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)
  · exact Or.inr (congrArg (fun A : Subgroup G => ⁅D.fullModule,A⁆) h)

theorem partner_pair (g : G) (hg : g ∈ D.maximalLocal) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj s.exchange).toMonoidHom =
      (MulAut.conj (g * s.exchange)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, he]
  exact selected_moved_pair s _
    (D.maximalLocal.mul_mem hg (le_normalizer_componentOrbit L T s.exchange_mem))

/-- The intersection of the exchanged factors belongs to the full fixed part. -/
theorem selected_pair_intersection_fixed :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let I := A ⊓ B
  have hn : D.maximalLocal ≤ normalizer (I : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (A ⊓ B).map (MulAut.conj g).toMonoidHom = A ⊓ B
    rw [map_inf _ _ _ (MulAut.conj g).injective]
    rcases selected_moved_pair s g hg with ha | ha <;>
      rcases partner_pair s g hg with hb | hb
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = A at ha
      change B.map _ = A at hb
      simp only [hb, he]
    · rw [ha, hb]
    · rw [ha, hb, inf_comm]
    · have he : A = B := map_injective (MulAut.conj g).injective (ha.trans hb.symm)
      change A.map _ = B at ha
      change B.map _ = B at hb
      simp only [hb, he]
  have hLC : L ≤ centralizer (I : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans s.crossed)
  have hTC : (T : Subgroup G) ≤ normalizer (centralizer (I : Set G) : Set G) :=
    ((le_normalizer_componentOrbit L T).trans hn).trans
      (normalizer_le_normalizer_centralizer _)
  exact le_inf (inf_le_left.trans (selected_moved_le s))
    (le_centralizer_iff.mpr (iSup_conjugates_le_of_le_normalizer _ _ _ hLC hTC))

/-- Vanishing of the full fixed part gives an internal direct product. -/
theorem selected_pair_disjoint
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Disjoint ⁅D.fullModule,L⁆
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
  disjoint_iff.mpr (bot_unique ((selected_pair_intersection_fixed s).trans_eq hz))

include s

/-- The specified exchange gives the literal two-component orbit. -/
theorem orbit_eq_pair :
    localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro t
    rcases source_nonnormal_maximal_pair D (selected_nonnormal s)
      s.exchange_mem s.exchange_moves t (le_normalizer_componentOrbit L T t.property)
      with h | h
    · exact h.le.trans le_sup_left
    · exact h.le.trans le_sup_right
  · refine sup_le (le_componentOrbit L T) ?_
    exact le_iSup (fun t : (T : Subgroup G) =>
      L.map (MulAut.conj (t : G)).toMonoidHom) ⟨s.exchange,s.exchange_mem⟩

/-- The first moved factor centralizes the exchanged component. -/
theorem moved_centralizes_partner_component :
    ⁅D.fullModule,L⁆ ≤ centralizer
      (L.map (MulAut.conj s.exchange).toMonoidHom : Set G) := by
  have hback : L.map (MulAut.conj s.exchange⁻¹).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    rcases source_nonnormal_maximal_pair D (selected_nonnormal s)
      s.exchange_mem s.exchange_moves s.exchange⁻¹
      (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem s.exchange_mem))
      with h | h
    · exact (s.exchange_moves (by simpa only [inv_inv] using
        (normalizer (L : Set G)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr h))).elim
    · exact h
  intro a ha
  rw [← hback]
  rintro _ ⟨l,hl,rfl⟩
  have hh := congrArg (MulAut.conj s.exchange⁻¹)
    (s.crossed (mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom ha) l hl)
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- The section denominator vanishes with the full fixed part. -/
theorem moved_fixed_eq_bot
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro x hx
  apply hz.le
  refine ⟨selected_moved_le s hx.1,?_⟩
  rw [orbit_eq_pair s]
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp (zpowers_le.mpr hx.2))
    (le_centralizer_iff.mp (zpowers_le.mpr (moved_centralizes_partner_component s hx.1))))
      (mem_zpowers x)

/-- The selected coordinates identify the original moved factor with the natural space. -/
def movedCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ↥(⁅D.fullModule,L⁆ : Subgroup G) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective s.natural.coordinates ⟨(MonoidHom.ker_eq_bot_iff _).mp
    (by rw [s.natural.kernel_eq, moved_fixed_eq_bot s hz, bot_subgroupOf]),s.natural.onto⟩

theorem movedCoordinates_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : ↥(⁅D.fullModule,L⁆ : Subgroup G)) :
    movedCoordinates s hz a = s.natural.coordinates a := by rfl

/-- The original natural moved factor has order eight. -/
theorem moved_card
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have hc := s.natural.card_section
  rw [moved_fixed_eq_bot s hz, card_bot] at hc
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc ⊢
  exact hc

private def pairFunction : (Eight × Eight) ≃* Space where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀ i : Bit, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;>
      simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' v w := by
    funext i
    by_cases hi : i = 1 <;> simp [hi]

private theorem factors_commute :
    ⁅D.fullModule,L⁆ ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  let _ : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm
    (⟨b,selected_partner_le s hb⟩ : D.fullModule) ⟨a,selected_moved_le s ha⟩)

/-- Multiplication of the actual factors, with its literal ambient formula. -/
def factorProduct
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (⁅D.fullModule,L⁆ : Subgroup G) ×
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* D.fullModule :=
  (Classical.choose (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (selected_pair_disjoint s hz) (factors_commute s))).trans
      (MulEquiv.subgroupCongr s.generated.symm)

theorem factorProduct_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) :
    (factorProduct s hz (a,b) : G) = (a : G) * b :=
  Classical.choose_spec (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (selected_pair_disjoint s hz) (factors_commute s)) a b

/-- Transport of the original coordinates through the specified exchange. -/
def partnerCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* Eight :=
  ((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆).symm.trans
    (movedCoordinates s hz)

theorem partnerCoordinates_conj
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G)) :
    partnerCoordinates s hz ((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆ a) =
      s.natural.coordinates a := by
  change movedCoordinates s hz
    (((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆).symm
      (((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆) a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Canonical full-module coordinates on the two original exchanged factors. -/
def fullCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    D.fullModule ≃* Space :=
  (factorProduct s hz).symm.trans
    (((movedCoordinates s hz).prodCongr (partnerCoordinates s hz)).trans pairFunction)

theorem fullCoordinates_mul
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
    fullCoordinates s hz
      ⟨(a : G) * b, D.fullModule.mul_mem (selected_moved_le s a.property)
        (selected_partner_le s b.property)⟩ i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  have he : (⟨(a : G) * b, D.fullModule.mul_mem (selected_moved_le s a.property)
      (selected_partner_le s b.property)⟩ : D.fullModule) = factorProduct s hz (a,b) :=
    Subtype.ext (factorProduct_apply s hz a b).symm
  rw [he]
  change pairFunction (((movedCoordinates s hz).prodCongr (partnerCoordinates s hz))
    ((factorProduct s hz).symm (factorProduct s hz (a,b)))) i = _
  rw [MulEquiv.symm_apply_apply]
  rfl


end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
