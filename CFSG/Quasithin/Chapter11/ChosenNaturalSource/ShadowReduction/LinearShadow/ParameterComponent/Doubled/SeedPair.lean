module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SeedCoordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.TINormalizerControl

/-!
# Complementary original seeds in the doubled module

The seed TI property and the orders q³ and q⁶ produce an actual complementary
normalizer conjugate. A local centralizer fixing a subgroup of corank at most
2n preserves both seeds. Their fixed subgroups split, so their centralizer
indices multiply and their binary coranks add on the literal full module.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SeedPair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

theorem seed_card (d : Coordinates D S) : Nat.card V = 2^(3*S.field.degree) := by
  obtain ⟨m,hm⟩ := d
  have h := Nat.card_congr (Equiv.ofBijective _ (SeedCoordinates.projection_bijective ⟨m,hm⟩ m))
  change Nat.card V = Nat.card (Fin 3 → S.field.Carrier) at h
  simpa only [Nat.card_fun,Nat.card_fin,S.field.card_eq,←pow_mul,
    Nat.mul_comm S.field.degree 3] using h

omit [Finite G] in
theorem conjugate_le (g : G) (hg : g ∈ normalizer (L : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ fullModule L V := by
  rw [←mem_normalizer_iff_map_conj_eq.mp (normalizes_fullModule hg)]
  exact map_mono seed_le_fullModule

theorem seed_ne_full (d : Coordinates D S) : V ≠ fullModule L V := by
  intro he
  have hc := congrArg (fun W : Subgroup G => Nat.card W) he
  rw [seed_card d,fullModule_card d] at hc
  have hh := hc.symm
  have := Nat.pow_right_injective (by decide : 2 ≤ 2) hh
  have := S.field.degree_pos
  omega

theorem exists_complement (d : Coordinates D S) :
    ∃ g ∈ normalizer (L : Set G),
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom = fullModule L V := by
  obtain ⟨g,hg,hne⟩ : ∃ g ∈ normalizer (L : Set G),
      V.map (MulAut.conj g).toMonoidHom ≠ V := by
    by_contra! hall
    apply seed_ne_full d
    apply le_antisymm seed_le_fullModule
    change Source.conjugateSpan (normalizer (L : Set G)) V ≤ V
    rw [Source.conjugateSpan]
    exact iSup_le fun g => (hall g g.property).le
  have hd : Disjoint V (V.map (MulAut.conj g).toMonoidHom) :=
    disjoint_iff.mpr ((LocalGeometry.Preliminary.seed_ti D S g hg).resolve_right hne)
  have hle := conjugate_le (V := V) g hg
  let := fullModule_elementary d
  have hn : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) :=
    (hle.trans ((fullModule L V).le_centralizer.trans (centralizer_le seed_le_fullModule))).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨g,hg,hd,eq_of_le_of_card_ge (sup_le seed_le_fullModule hle) ?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint V _ hn hd,
    card_map_of_injective (MulAut.conj g).injective,seed_card d,fullModule_card d,←pow_add]
  have he : 3*S.field.degree + 3*S.field.degree = 6*S.field.degree := by omega
  rw [he]

theorem seed_inter_ne_bot (d : Coordinates D S) {U : Subgroup G}
    (hU : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) : V ⊓ U ≠ ⊥ := by
  intro hz
  have hidx : U.relIndex V ≤ U.relIndex (fullModule L V) :=
    relIndex_le_of_le_right seed_le_fullModule (by
      intro hz
      have hh := U.relIndex_dvd_card (fullModule L V)
      rw [hz,zero_dvd_iff] at hh
      exact Nat.card_pos.ne' hh)
  have hh := Nat.log_mono_right hidx (b := 2)
  rw [←inf_relIndex_right U V,inf_comm U V,hz,relIndex_bot_left,seed_card d,
    Nat.log_pow (by decide)] at hh
  change 3*S.field.degree ≤ subgroupCorank (fullModule L V) U at hh
  have := S.field.degree_pos
  omega

theorem local_centralizer_normalizes (d : Coordinates D S) {U : Subgroup G}
    (hU : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G) :=
  (inf_le_inf_left _ (centralizer_le (show V ⊓ U ≤ U from inf_le_right))).trans
    (inf_centralizer_le_normalizer_of_trivial_intersections
      (LocalGeometry.Preliminary.seed_ti D S) (seed_inter_ne_bot d hU) inf_le_left)

omit [Finite G] in
theorem conjugate_corank (g : G)
    (hg : g ∈ normalizer (L : Set G)) (U : Subgroup G) :
    subgroupCorank (fullModule L V) (U.map (MulAut.conj g).toMonoidHom) =
      subgroupCorank (fullModule L V) U := by
  have he : (fullModule L V).map (MulAut.conj g).toMonoidHom = fullModule L V :=
    mem_normalizer_iff_map_conj_eq.mp (normalizes_fullModule hg)
  unfold subgroupCorank
  conv_lhs => rw [←he]
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem local_centralizer_normalizes_conjugate (d : Coordinates D S)
    {U : Subgroup G} (hU : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree)
    (g : G) (hg : g ∈ normalizer (L : Set G)) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤
      normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  have hM : (normalizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom = normalizer (L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).le_normalizer
      ((normalizer (L : Set G)).inv_mem hg))
  have hc : C.map (MulAut.conj g⁻¹).toMonoidHom ≤
      normalizer (L : Set G) ⊓ centralizer (U.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Theory.GroupTheory.map_centralizer_equiv,
      hM]
    exact le_rfl
  have hh := hc.trans (local_centralizer_normalizes d
    (by rw [conjugate_corank g⁻¹ ((normalizer (L : Set G)).inv_mem hg)]; exact hU))
  have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hh).trans
    (V.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hcancel : (C.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = C := by
    simpa only [inv_inv] using offender_map_conj_inverse C g⁻¹
  rwa [hcancel] at hm

/-- A small-corank local centralizer preserves an actual direct pair of
conjugates of the original seed. -/
theorem local_centralizer_preserves_pair (d : Coordinates D S) {U : Subgroup G}
    (hU : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    ∃ g ∈ normalizer (L : Set G),
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom = fullModule L V ∧
      normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤
        normalizer (V : Set G) ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨g,hg,hd,hs⟩ := exists_complement d
  exact ⟨g,hg,hd,hs,le_inf (local_centralizer_normalizes d hU)
    (local_centralizer_normalizes_conjugate d hU g hg)⟩

omit [Finite G] in
private theorem centralizer_split {B A : Subgroup G}
    (hd : Disjoint V B) (hn : B ≤ normalizer (V : Set G))
    (haV : A ≤ normalizer (V : Set G)) (haB : A ≤ normalizer (B : Set G)) :
    (V ⊔ B) ⊓ centralizer (A : Set G) =
      (V ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (A : Set G)) := by
  apply le_antisymm ?_ (sup_le (inf_le_inf le_sup_left le_rfl)
    (inf_le_inf le_sup_right le_rfl))
  rintro x ⟨hx,hxc⟩
  have hx' : x ∈ (V : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left V B hn]
    exact hx
  obtain ⟨v,hv,b,hb,rfl⟩ := hx'
  have he (a : G) (ha : a ∈ A) :
      ((⟨a*v*a⁻¹,(mem_normalizer_iff.mp (haV ha) v).mp hv⟩,
        ⟨a*b*a⁻¹,(mem_normalizer_iff.mp (haB ha) b).mp hb⟩) : V × B) =
      (⟨v,hv⟩,⟨b,hb⟩) := by
    apply mul_injective_of_disjoint hd
    change (a*v*a⁻¹)*(a*b*a⁻¹) = v*b
    calc
      _ = a*(v*b)*a⁻¹ := by group
      _ = v*b := by rw [hxc a ha,mul_inv_cancel_right]
  have hvC : v ∈ centralizer (A : Set G) := by
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : V × B => (z.1:G)) (he a ha))
  have hbC : b ∈ centralizer (A : Set G) := by
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : V × B => (z.2:G)) (he a ha))
  exact mul_mem_sup ⟨hv,hvC⟩ ⟨hb,hbC⟩

/-- Centralizer indices multiply across the actual complementary seeds. -/
theorem fixed_index_product (d : Coordinates D S) {B A : Subgroup G}
    (hd : Disjoint V B) (hs : V ⊔ B = fullModule L V)
    (haV : A ≤ normalizer (V : Set G)) (haB : A ≤ normalizer (B : Set G)) :
    (centralizer (A : Set G)).relIndex (fullModule L V) =
      (centralizer (A : Set G)).relIndex V * (centralizer (A : Set G)).relIndex B := by
  let := fullModule_elementary d
  have hVW : V ≤ fullModule L V := hs ▸ le_sup_left
  have hBW : B ≤ fullModule L V := hs ▸ le_sup_right
  have hn : B ≤ normalizer (V : Set G) :=
    (hBW.trans ((fullModule L V).le_centralizer.trans (centralizer_le hVW))).trans
      (Subgroup.centralizer_le_normalizer _)
  let C := centralizer (A : Set G)
  have hdc : Disjoint (V ⊓ C) (B ⊓ C) := hd.mono inf_le_left inf_le_left
  have hnc : B ⊓ C ≤ normalizer (V ⊓ C : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact (inf_le_left.trans hBW).trans ((fullModule L V).le_centralizer.trans
      (centralizer_le (inf_le_left.trans hVW)))
  have hsplit : fullModule L V ⊓ C = (V ⊓ C) ⊔ (B ⊓ C) :=
    hs ▸ centralizer_split hd hn haV haB
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (V ⊓ C) (B ⊓ C) hnc hdc
  rw [←hsplit] at hc
  have hw := card_sup_eq_mul_of_normalizes_of_disjoint V B hn hd
  rw [hs] at hw
  have hWidx := relIndex_mul_card_of_le (show fullModule L V ⊓ C ≤ fullModule L V from inf_le_left)
  have hVidx := relIndex_mul_card_of_le (show V ⊓ C ≤ V from inf_le_left)
  have hBidx := relIndex_mul_card_of_le (show B ⊓ C ≤ B from inf_le_left)
  rw [inf_relIndex_left] at hWidx hVidx hBidx
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(fullModule L V ⊓ C)))
  calc
    _ = Nat.card (fullModule L V) := hWidx
    _ = Nat.card V * Nat.card B := hw
    _ = _ := by rw [←hVidx,←hBidx,hc]; ring

/-- The original centralizer's binary corank is the sum of its coranks on
these two literal conjugates. -/
theorem fixed_corank_sum (d : Coordinates D S) {B A : Subgroup G}
    (hd : Disjoint V B) (hs : V ⊔ B = fullModule L V)
    (haV : A ≤ normalizer (V : Set G)) (haB : A ≤ normalizer (B : Set G)) :
    subgroupCorank (fullModule L V) (fullModule L V ⊓ centralizer (A : Set G)) =
      subgroupCorank V (V ⊓ centralizer (A : Set G)) +
        subgroupCorank B (B ⊓ centralizer (A : Set G)) := by
  let := fullModule_elementary d
  let := D.elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion (show B ≤ fullModule L V from hs ▸ le_sup_right)) (inclusion_injective _)
  have he := fixed_index_product d hd hs haV haB
  have hp (W : Subgroup G) [IsElementaryAbelian 2 W] :
      (centralizer (A : Set G)).relIndex W =
        2^subgroupCorank W (W ⊓ centralizer (A : Set G)) := by
    rw [relIndex_eq_two_pow_quotient_finrank,←subgroupCorank_eq_quotient_finrank]
    simp only [subgroupCorank,inf_relIndex_left]
  rw [hp,hp,hp,←pow_add] at he
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) he

/-- Literal source consumer: the pointwise centralizer preserving the original
pair has total seed displacement at most the given 2n corank. -/
theorem local_centralizer_corank_budget (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    ∃ g ∈ normalizer (L : Set G),
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom = fullModule L V ∧
      let A := normalizer (L : Set G) ⊓ centralizer (U : Set G)
      subgroupCorank V (V ⊓ centralizer (A : Set G)) +
        subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
          (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G)) ≤ 2*S.field.degree := by
  obtain ⟨g,hg,hd,hs,hn⟩ := local_centralizer_preserves_pair d hc
  refine ⟨g,hg,hd,hs,?_⟩
  dsimp only
  rw [←fixed_corank_sum d hd hs (hn.trans inf_le_left) (hn.trans inf_le_right)]
  exact (ChapterE.Section06.subgroupCorank_antitone
    (le_inf hU (le_centralizer_iff.mpr inf_le_right))).trans hc

end SeedPair
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled

