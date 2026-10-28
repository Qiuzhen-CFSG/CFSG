module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Radicals
import all CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.Comparison
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Orbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Fixer

/-!
# The actual Sp₄(4) displacement bound

For Q = [X,T], the original marked image lies in the selected parabolic
radical, of order at most q³; its kernel lies in O₂(L). Shortness identifies
O₂(L) with the whole chosen seed. The established central-cover cohomology
bound gives |V| ≤ q⁵, including its nonsplit central part. Hence |Q| ≤ 2¹⁶
at q=4. The final theorem applies this to the actual J₁ order obstruction.

The private image body is used through the same intentional companion
boundary as Sp4Radicals. Shortness remains the output of the shared
qt-c132-nonbinary-symplectic producer. The companion Sp4Movement supplies residual movement; final assembly
remains with qt-d-1222-natural-line-action; this is not unconditional
Sylow-normalizer containment.
Source: Aschbacher--Smith 3.3.16, p.591, using I.1.6 and 11.0.3(3).
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
open PointCohomology.PointGeometry.Sp4Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private theorem point_radical_card_le :
    Nat.card (pointRadical (F := S.field.Carrier)) ≤ Nat.card S.field.Carrier ^ 3 := by
  let j : pointRadical (F := S.field.Carrier) →
      S.field.Carrier × S.field.Carrier × S.field.Carrier := fun g =>
    (g.val.val.val (.inl 1) (.inr 0), g.val.val.val (.inr 1) (.inr 0),
      g.val.val.val (.inl 0) (.inr 0))
  have hj : Function.Injective j := by
    intro g h he
    apply Subtype.ext
    rw [pointRadical_eq_element g.val g.property, pointRadical_eq_element h.val h.property]
    rw [show g.val.val.val (.inl 1) (.inr 0) = h.val.val.val (.inl 1) (.inr 0)
      from congrArg Prod.fst he,
      show g.val.val.val (.inr 1) (.inr 0) = h.val.val.val (.inr 1) (.inr 0)
      from congrArg (fun t => t.2.1) he,
      show g.val.val.val (.inl 0) (.inr 0) = h.val.val.val (.inl 0) (.inr 0)
      from congrArg (fun t => t.2.2) he]
  have hh := Nat.card_le_card_of_injective j hj
  simpa only [Nat.card_prod,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

/-- The quotient two-core has at most three field coordinates at either flag index. -/
theorem flag_model_core_card_le (f : InvariantFlag (Coordinates.sp4 m)) (i : Fin 2) :
    Nat.card ((modelImage D S m (f.Li i)).pCoreIn 2) ≤ Nat.card S.field.Carrier ^ 3 := by
  fin_cases i
  · change Nat.card ((modelImage D S m (f.Li 0)).pCoreIn 2) ≤ _
    rw [modelImage_point D S m f, ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective,
      card_map_of_injective (MulAut.conj (Sp4.alignment m)).injective]
    change Nat.card ((pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype) ≤ _
    rw [pointLocal_core_eq S.field.card_eq S.nonbinary,
      card_map_of_injective pointLocal.subtype_injective]
    exact point_radical_card_le D S
  · change Nat.card ((modelImage D S m (f.Li 1)).pCoreIn 2) ≤ _
    rw [modelImage_plane D S m f, ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective,
      card_map_of_injective (MulAut.conj (Sp4.alignment m)).injective]
    change Nat.card ((pCore 2 (planeLocal (F := S.field.Carrier))).map planeLocal.subtype) ≤ _
    rw [planeLocal_core_eq S.field.card_eq S.nonbinary,
      card_map_of_injective planeLocal.subtype_injective]
    exact (EvenTwoRank.card_plane_radical).le

/-- The displacement belongs to the original L, before passing to any model. -/
theorem displacement_le_component {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) : E.displacement ≤ L :=
  (commutator_mono (inf_le_left.trans inf_le_right) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp D.sylow_normalizes_component)

/-- Its image lies in the actual local quotient two-core, at the selected index. -/
theorem displacement_modelImage_le {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    modelImage D S m E.displacement ≤ (modelImage D S m (f.Li E.index)).pCoreIn 2 := by
  have hh : image D S m (Sp4.alignment m)⁻¹ E.displacement ≤
      image D S m (Sp4.alignment m)⁻¹ ((f.Li E.index).pCoreIn 2) :=
    (map_mono (comap_mono E.displacement_le_source_radical)).trans
      (flag_radical_image_le_local_core D S m f E.index)
  have hYL : f.Li E.index ≤ L := (localResidual_le _).trans inf_le_left
  rw [image_component D S m _ _ (displacement_le_component D S m E),
    image_component D S m _ _ ((pCoreIn_le 2 _).trans hYL),
    modelImage_core D S m _ hYL] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj (Sp4.alignment m)⁻¹).injective).mp
    ((map_le_map_iff_of_injective inner_injective).mp hh)

/-- The literal displacement has order at most q³ times the original two-core. -/
theorem displacement_card_le_core {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    Nat.card E.displacement ≤ Nat.card (pCore 2 L) * Nat.card S.field.Carrier ^ 3 := by
  let hQL := displacement_le_component D S m E
  let q := (Coordinates.sp4 m).quotientMap
  let b : E.displacement →* Sp S.field.Carrier := q.comp (inclusion hQL)
  have hker : Nat.card b.ker ≤ Nat.card (pCore 2 L) := by
    let j : b.ker → pCore 2 L := fun x => ⟨inclusion hQL x, by
      apply (QuotientGroup.eq_one_iff _).mp
      apply m.groupEquiv.injective
      exact x.property.trans m.groupEquiv.map_one.symm⟩
    apply Nat.card_le_card_of_injective j
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 L => (z.val : G)) hxy
  have hrange : b.range = modelImage D S m E.displacement := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨inclusion hQL z,z.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  have hcard : Nat.card E.displacement = Nat.card b.ker * Nat.card b.range := by
    rw [←index_ker]
    exact b.ker.card_mul_index.symm
  rw [hcard,hrange]
  exact Nat.mul_le_mul hker ((card_le_of_le (displacement_modelImage_le D S m E)).trans
    (flag_model_core_card_le D S m f E.index))

/-- At the exceptional field order, only the intrinsic block core bound remains. -/
theorem displacement_card_le_sixteen {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
    (hcore : Nat.card (pCore 2 L) ≤ 2 ^ 10) :
    Nat.card E.displacement ≤ 2 ^ 16 := by
  have hF : Nat.card S.field.Carrier = 4 := by rw [S.field.card_eq,E.degree_eq_two]; rfl
  have hh := displacement_card_le_core D S m E
  rw [hF] at hh
  exact hh.trans ((Nat.mul_le_mul_right 64 hcore).trans_eq (by norm_num))

include D S m in
/-- The entire chosen module, including its central part, has at most q⁵ elements. -/
theorem seed_card_le_five : Nat.card V ≤ 2 ^ (5 * S.field.degree) := by
  have hk := Preliminary.sp4_centralizer_rank_le D S m
  rw [Preliminary.centralizer_rank_eq_kernel_finrank D m] at hk
  have hn := Representation.OneCohomology.coefficient_finrank_of_card 2 S.field.degree S.field.card_eq
  have hw : Module.finrank (ZMod 2) ((Fin 2 ⊕ Fin 2) → S.field.Carrier) =
      4 * S.field.degree := by
    rw [Module.finrank_pi_fintype]
    simp only [hn,Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,
      smul_eq_mul]
  have he := (Preliminary.markedProjection D m).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (Preliminary.markedProjection_isCover D m).1,
    finrank_top,hw] at he
  have hd : Module.finrank (ZMod 2) D.space ≤ 5 * S.field.degree := by omega
  rw [← Nat.card_congr D.spaceEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative D.space ≃ D.space),
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hd

include D S m in
/-- Shortness identifies O₂(L) with the original seed in the symplectic row. -/
theorem intrinsic_core_eq_seed (hb : ChapterC.IsShort L) : L.pCoreIn 2 = V := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2 : ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  rw [PointBlocks.seed_eq_blockU D hb]
  exact congrArg (map L.subtype)
    (ChapterC.RankTwo.Sp4Four.core_eq_blockU_of_symplectic_quotient hF m.groupEquiv)

/-- The source's 2¹⁰ core bound follows from shortness and the actual natural cover. -/
theorem intrinsic_core_card_le_ten {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (hb : ChapterC.IsShort L) :
    Nat.card (pCore 2 L) ≤ 2 ^ 10 := by
  have he : Nat.card (pCore 2 L) = Nat.card V := by
    rw [←intrinsic_core_eq_seed D S m hb,Subgroup.pCoreIn,
      card_map_of_injective L.subtype_injective]
  rw [he]
  have hh := seed_card_le_five D S m
  simpa only [E.degree_eq_two] using hh

/-- The full numerical displacement bound on the original field-four configuration. -/
theorem displacement_card_le_of_short {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (hb : ChapterC.IsShort L) :
    Nat.card E.displacement ≤ 2 ^ 16 :=
  displacement_card_le_sixteen D S m E (intrinsic_core_card_le_ten D S m E hb)

/-- Apply the proved bound to the literal J₁ terminal contradiction.
Sp4Movement discharges movement; shortness is the shared MS block producer’s output. -/
theorem false_of_short_moved_displacement {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (hb : ChapterC.IsShort L)
    (hmoves : ¬ f.Li E.index ≤ centralizer (E.displacement : Set G)) : False :=
  E.false_of_small_moved_displacement (displacement_card_le_of_short D S m E hb) hmoves


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
