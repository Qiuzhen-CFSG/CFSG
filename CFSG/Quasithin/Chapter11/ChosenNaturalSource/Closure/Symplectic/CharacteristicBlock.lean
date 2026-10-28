module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoreAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Action

/-!
# Characteristic subgroups in the original symplectic closure reduction

For Q₁ = O₂(G₁), the native point-radical lattice gives the root-image and
full-radical-image alternatives. In the latter case the nonbinary point
commutator calculation gives the full action image of [Q₁,L₁]. This
commutator lies in Q₁ ∩ L; the original action kernel O₂(L) then proves
R₁ ∩ LQ₁ = Q₁, using the already established O₂(L) ≤ Q₁.

A characteristic subgroup of Q₁ is normalized by G₁. If L also normalizes
it, the genuine preceding normalizer-control theorem forces G₁ into M,
contradicting 11.5.4. We transport this exclusion to the intrinsic Q₁ in
LQ₁, proving exactly MS3. Three original opposite-pair conjugates give
LT = ⟨I,L₁T⟩, so the same exclusion applies to the marked pair I.

The source application discharges the initial radical-action and
opposite-core inputs. The OddIndex extension supplies MS2(a) in the full-image
case. The root-image case still requires C.1.29, and the C.1.32 block conclusion
remains with qt-d-1222-natural-closure-sp4. This module does not assert 11.5.7
or assume its block or abelianness conclusion.

Source: Aschbacher--Smith, 11.5.7, printed p.783; C.1.31(MS3), p.135.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Normality of Q₁ is relative to the actual point normalizer. -/
theorem point_normalizer_normalizes_core :
    E.G₁ ≤ normalizer (E.G₁.pCoreIn 2 : Set G) :=
  E.G₁.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E.G₁ (pCore 2 E.G₁))

/-- The original Q₁ image has precisely the two source alternatives;
nonabelianness of the closure excludes its trivial image. -/
theorem core_image_alternatives (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (hne : ¬ IsMulCommutative E.W) :
    actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∨
    actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁ := by
  have hQ : actionImage (V := V) (E.G₁.pCoreIn 2) ≤
      actionImage (V := V) (E.L₁.pCoreIn 2) :=
    (image_mono (core_le_local_radical E m)).trans (FullAmbient.radical_image_le m g hpoint)
  have hlocal := PointModel.local_identification m g hpoint
  rcases FullAction.invariant_lattice m g hlocal hcartan hXL _ hQ
    (image_normalizes _ _ ((sup_le E.L₁_le_G₁ hXG).trans
      (point_normalizer_normalizes_core E))) with hz | hz | hz
  · have hwz : actionImage (V := V) E.W = ⊥ :=
      bot_unique ((image_mono hW).trans_eq hz)
    exact (W_actionImage_ne_bot_of_nonabelian E m E.input.sylow_normalizes hW hne hwz).elim
  · exact Or.inl hz
  · right
    apply le_antisymm (image_mono (core_le_local_radical E m))
    exact (FullAmbient.radical_image_le m g hpoint).trans_eq hz.symm

/-- Characteristic subgroups of Q₁ cannot be normalized by L. -/
theorem characteristic_not_normalized (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (C : Subgroup (E.G₁.pCoreIn 2)) [C.Characteristic] (hne : C ≠ ⊥) :
    ¬ L ≤ normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) := by
  intro hn
  have hG : E.G₁ ≤ normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) :=
    (point_normalizer_normalizes_core E).trans
      (normalizer_le_normalizer_characteristic_image _ C)
  have hne' : C.map (E.G₁.pCoreIn 2).subtype ≠ ⊥ := fun h =>
    hne ((C.map_eq_bot_iff_of_injective (E.G₁.pCoreIn 2).subtype_injective).mp h)
  have hc := D.normal_subgroup_normalizer_le E.input.source.toHypothesis1221
    ((map_subtype_le C).trans ((core_le_sylow E m).trans le_sup_right)) hne'
    (sup_le hn (m.sylow_le_point_normalizer.trans hG))
  exact hout ((Subgroup.centralizer_le_normalizer _).trans (hG.trans hc))

/-- The same exclusion applies to a root-pair join generating LT with L₁T. -/
theorem characteristic_not_normalized_by_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (I : Subgroup G) (hgen : L ≤ I ⊔ (E.L₁ ⊔ (T : Subgroup G)))
    (C : Subgroup (E.G₁.pCoreIn 2)) [C.Characteristic] (hne : C ≠ ⊥) :
    ¬ I ≤ normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) := by
  intro hn
  apply characteristic_not_normalized E m hout C hne
  apply hgen.trans
  exact sup_le hn ((sup_le E.L₁_le_G₁ m.sylow_le_point_normalizer).trans
    ((point_normalizer_normalizes_core E).trans
      (normalizer_le_normalizer_characteristic_image _ C)))

/-- MS3 in the literal overgroup LQ₁, with characteristicness inside Q₁. -/
theorem msCharacteristic (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M) :
    ChapterC.MSCharacteristicCondition
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) := by
  let J := L ⊔ E.G₁.pCoreIn 2
  let R := (E.G₁.pCoreIn 2).subgroupOf J
  intro C hC hne hn
  let := hC
  let B := (C.map R.subtype).map J.subtype
  have hR : R.map J.subtype = E.G₁.pCoreIn 2 := map_subgroupOf_eq_of_le le_sup_right
  have hG : E.G₁ ≤ normalizer (B : Set G) := by
    have hh := normalizer_le_normalizer_characteristic_map J.subtype J.subtype_injective R C
    rw [hR] at hh
    exact (point_normalizer_normalizes_core E).trans hh
  have hJ : J ≤ normalizer (B : Set G) := by
    let := hn
    have hh := (C.map R.subtype).le_normalizer_map J.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  have hB : B ≤ L ⊔ (T : Subgroup G) :=
    ((map_mono (map_subtype_le C)).trans hR.le).trans
      ((core_le_sylow E m).trans le_sup_right)
  have hBne : B ≠ ⊥ := by
    intro hb
    have hb' := ((C.map R.subtype).map_eq_bot_iff_of_injective J.subtype_injective).mp hb
    exact hne ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp hb')
  have hc := D.normal_subgroup_normalizer_le E.input.source.toHypothesis1221 hB hBne
    (sup_le (le_sup_left.trans hJ) (m.sylow_le_point_normalizer.trans hG))
  exact hout ((Subgroup.centralizer_le_normalizer _).trans (hG.trans hc))

/-- The native nonbinary point commutator identity on the full original
normalizer action, including its central attachment. -/
theorem local_core_image_commutator (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    ⁅actionImage (V := V) (E.L₁.pCoreIn 2),actionImage (V := V) E.L₁⁆ =
      actionImage (V := V) (E.L₁.pCoreIn 2) := by
  have hn : ⁅(pointLocal (F := E.input.field.Carrier)).pCoreIn 2,pointLocal⁆ =
      (pointLocal (F := E.input.field.Carrier)).pCoreIn 2 := by
    have he := pointLocal_core_commutator E.input.field.card_eq E.input.nonbinary
    rw [← pointLocal_core_eq E.input.field.card_eq E.input.nonbinary] at he
    have hm := congrArg (map (pointLocal (F := E.input.field.Carrier)).subtype) he
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm
  have hlocal := PointModel.local_identification m g hpoint
  rw [← FullAction.image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le),
    ← FullAction.image_eq m _ E.L₁_le, ← map_commutator,
    PointModel.image_core m E.L₁ E.L₁_le, hlocal,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    ← map_commutator, hn]

/-- In the full-image case the actual core-local commutator has the entire
radical image and lies in both Q₁ and L. -/
theorem core_local_commutator (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hfull : actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁) :
    ⁅E.G₁.pCoreIn 2,E.L₁⁆ ≤ E.G₁.pCoreIn 2 ⊓ L ∧
      actionImage (V := V) ⁅E.G₁.pCoreIn 2,E.L₁⁆ = actionImage (V := V) E.R₁ := by
  have hQN := core_normalizes_seed E m E.input.sylow_normalizes
  have hQC : E.G₁.pCoreIn 2 ≤ normalizer (L : Set G) :=
    (core_le_sylow E m).trans D.sylow_normalizes_component
  have hlocalR : actionImage (V := V) (E.L₁.pCoreIn 2) ≤ actionImage (V := V) E.R₁ := by
    have hn := LocalGeometry.sylow_normalizes_localResidual D E.V₁
      m.sylow_le_point_normalizer
    have hc : E.L₁.pCoreIn 2 ≤ E.R₁ :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le E.L₁.le_normalizer hn)
    exact image_mono hc
  have heR : actionImage (V := V) E.R₁ = actionImage (V := V) (E.L₁.pCoreIn 2) :=
    le_antisymm (FullAmbient.radical_image_le m g hpoint) hlocalR
  refine ⟨le_inf ?_ ?_,?_⟩
  · exact le_normalizer_iff_commutator_le_left.mp
      (E.L₁_le_G₁.trans (point_normalizer_normalizes_core E))
  · exact (commutator_mono le_rfl E.L₁_le).trans
      (le_normalizer_iff_commutator_le_right.mp hQC)
  · rw [Terminal.actionImage_commutator V _ _ hQN (E.L₁_le.trans D.normalizes),
      hfull, heR, local_core_image_commutator E m g hpoint]

/-- The original action kernel and the core-local commutator give the exact
intersection required by the MS-pair application. -/
theorem radical_intersection_join_eq (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hfull : actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁) :
    E.R₁ ⊓ (L ⊔ E.G₁.pCoreIn 2) = E.G₁.pCoreIn 2 := by
  obtain ⟨hC,heC⟩ := core_local_commutator E m g hpoint hfull
  let C := ⁅E.G₁.pCoreIn 2,E.L₁⁆
  have hCL : C ≤ L := hC.trans inf_le_right
  have hCQ : C ≤ E.G₁.pCoreIn 2 := hC.trans inf_le_left
  have hQN : E.G₁.pCoreIn 2 ≤ normalizer (L : Set G) :=
    (core_le_sylow E m).trans D.sylow_normalizes_component
  have hRL : E.R₁ ⊓ L ≤ E.G₁.pCoreIn 2 := by
    rintro x ⟨hxR,hxL⟩
    have hxN : x ∈ normalizer (V : Set G) := D.normalizes hxL
    have hm : V.normalizerMonoidHom ⟨x,hxN⟩ ∈ actionImage (V := V) C := by
      rw [heC]
      exact mem_map_of_mem _ (show (⟨x,hxN⟩ : normalizer (V : Set G)) ∈
        E.R₁.subgroupOf _ from hxR)
    obtain ⟨c,hc,he⟩ := hm
    let xL : L := ⟨x,hxL⟩
    let cL : L := ⟨c.val,hCL hc⟩
    have he' : FullAction.componentHom (D := D) cL =
        FullAction.componentHom (D := D) xL := he
    have hk : xL*cL⁻¹ ∈ (FullAction.componentHom (D := D)).ker := by
      change FullAction.componentHom (D := D) (xL*cL⁻¹) = 1
      rw [map_mul,map_inv,he',mul_inv_cancel]
    rw [FullAction.componentHom_ker E] at hk
    have hxq : x*c.val⁻¹ ∈ E.G₁.pCoreIn 2 :=
      hcore (mem_map_of_mem L.subtype hk)
    have hh := (E.G₁.pCoreIn 2).mul_mem hxq (hCQ hc)
    change x*c.val⁻¹*c.val ∈ E.G₁.pCoreIn 2 at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  apply le_antisymm _ (le_inf (core_le_local_radical E m) le_sup_right)
  rintro x ⟨hxR,hxJ⟩
  change x ∈ (↑(L ⊔ E.G₁.pCoreIn 2) : Set G) at hxJ
  rw [coe_mul_of_right_le_normalizer_left L _ hQN] at hxJ
  obtain ⟨l,hl,q,hq,rfl⟩ := hxJ
  have hlR : l ∈ E.R₁ := by
    simpa only [mul_assoc,mul_inv_cancel,mul_one] using
      E.R₁.mul_mem hxR (E.R₁.inv_mem (core_le_local_radical E m hq))
  exact (E.G₁.pCoreIn 2).mul_mem (hRL ⟨hlR,hl⟩) hq

/-- The original initial branch supplies every radical-action and core input
for the characteristic reduction. Only the root-image branch and the genuine
rank-two pushing-up classification remain after this theorem. -/
theorem characteristic_reduction_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
      L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 ∧
      ChapterC.MSCharacteristicCondition
        ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) ∧
      (actionImage (V := V) (E.G₁.pCoreIn 2) =
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∨
       (actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁ ∧
        E.R₁ ⊓ (L ⊔ E.G₁.pCoreIn 2) = E.G₁.pCoreIn 2)) := by
  obtain ⟨hV,hW,hU,hcore⟩ := initial_and_opposite_core_of_preceding E m g hpoint
    hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive hne
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  refine ⟨hV,hW,hU,hcore,msCharacteristic E m hout,?_⟩
  rcases core_image_alternatives E m g hpoint hcartan hXL hXG hW hne with hr | hf
  · exact Or.inl hr
  · exact Or.inr ⟨hf,radical_intersection_join_eq E m g hpoint hcore hf⟩

/-- The actual three opposite-pair conjugates and the original Sylow group
supply precisely the large-local generation used in the characteristic
subgroup exclusion. -/
theorem opposite_pair_generates_large_local (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
        (FullAction.modelHom m)) :
    L ⊔ (T : Subgroup G) = oppositeJoin (auxiliaryW E) y ⊔
      (E.L₁ ⊔ (T : Subgroup G)) := by
  let I := oppositeJoin (auxiliaryW E) y
  let J := I ⊔ (E.L₁ ⊔ (T : Subgroup G))
  change L ⊔ (T : Subgroup G) = J
  have hIJ : I ≤ J := le_sup_left
  have hLJ : E.L₁ ≤ J := le_sup_left.trans le_sup_right
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  obtain ⟨l,hl,hgen⟩ := OppositeGeometry.three_conjugates_of_marked_pair E m hW hy
    g hlocal hpair
  have hconj (i : Fin 3) : I.map (MulAut.conj (l i)).toMonoidHom ≤ J := by
    exact (map_mono hIJ).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer (hLJ (hl i))))
  have hS : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hL : L ≤ J := hgen.trans (sup_le (iSup_le hconj) (hS.trans hTJ))
  have hWT : auxiliaryW E ≤ (T : Subgroup G) :=
    (auxiliaryW_containment_and_normalization E hW).2.1.trans (core_le_sylow E m)
  have hWL : auxiliaryW E ≤ L ⊔ (T : Subgroup G) := hWT.trans le_sup_right
  have hIL : I ≤ L ⊔ (T : Subgroup G) := by
    apply sup_le hWL
    exact (map_mono hWL).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hy)))
  exact le_antisymm (sup_le hL hTJ) (sup_le hIL (sup_le_sup_right E.L₁_le (T : Subgroup G)))

/-- The C.1.29 characteristic alternative is impossible for this very
marked opposite pair. No generation or ambient normality premise is added. -/
theorem characteristic_not_normalized_by_marked_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map
        (FullAction.modelHom m))
    (C : Subgroup (E.G₁.pCoreIn 2)) [C.Characteristic] (hne : C ≠ ⊥) :
    ¬ oppositeJoin (auxiliaryW E) y ≤
      normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) :=
  characteristic_not_normalized_by_pair E m hout _
    (le_sup_left.trans_eq (opposite_pair_generates_large_local E m hW hy g hlocal hpair))
    C hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
