module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityAmbientSylow
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizerBounds

/-!
# Exact short-root centralizers in the triality common Sylow

In the genuine positive-root coordinates, an element commutes with the
marked short root precisely when its first two cubic coordinates have trace
zero. Each trace kernel has order q². The remaining cubic coordinate and
three base-field coordinates are free, giving q² q² q³ q³ = q¹⁰.

The original right-parabolic comparison transports this exact count to the
literal source S. The proved S=T then gives the long and short centralizer
orders q¹² and q¹⁰ in the original ambient Sylow. This calculation alone
does not assert that the short centralizer is Sylow in its full centralizer.
Model extremality, F.4.42 ambient containment and F.4.43 order comparison
are separate steps in the generic-global assembly.

Source: Aschbacher--Smith F.4.27 and F.4.40, printed pp.288--289 and 294,
and 5.3.3, p.659 (`refs/quasithin.pdf`); the cubic root relations follow
GLS3 §§2.4--2.6. The internal import reuses the faithful centralizer
transport through the same original map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Triality.Standard.CentralCovers.TwoPrimary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortSylow

private def sparam (P : Parameters) : ArmsParameters P := (![0,1],![0,0,0])
private theorem sval (P : Parameters) (hp : P.prime=2) :
    (armsCoordinates P hp (sparam P)).val=short P hp 2 1 := by
  rw [armsCoordinates_factorization]
  simp [sparam]

private theorem amul (P : Parameters) (hp : P.prime=2) (v w : ArmsParameters P) :
    (armsCoordinates P hp (armsMultiply P v w)).val =
      (armsCoordinates P hp v).val * (armsCoordinates P hp w).val := by
  exact congrArg Subtype.val (armsEquiv_multiply P hp v w)

private theorem commutes_iff (P : Parameters) (hp : P.prime=2)
    (a : ExtensionField P) (v : ArmsParameters P) :
    (short P hp 0 a * (armsCoordinates P hp v).val) * short P hp 2 1 =
      short P hp 2 1 * (short P hp 0 a * (armsCoordinates P hp v).val) ↔
    armsPairing P a 1 = 0 ∧ armsPairing P (v.1 0) 1 = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hs := short_self_inverse P hp a
  have hshear : (short P hp 0 a)⁻¹ * short P hp 2 1 * short P hp 0 a =
      (armsCoordinates P hp (shearParameters P a (sparam P))).val := by
    have hh := short_shear P hp a (sparam P)
    rw [sval P hp] at hh
    simpa only [hs] using hh
  have he : (short P hp 0 a * (armsCoordinates P hp v).val) * short P hp 2 1 =
      short P hp 2 1 * (short P hp 0 a * (armsCoordinates P hp v).val) ↔
      armsMultiply P v (sparam P) = armsMultiply P (shearParameters P a (sparam P)) v := by
    rw [←(armsCoordinates P hp).injective.eq_iff]
    rw [Subtype.ext_iff,amul,amul,sval]
    rw [←hshear]
    constructor <;> intro h
    · calc
        _ = (short P hp 0 a)⁻¹ * ((short P hp 0 a * (armsCoordinates P hp v).val) * short P hp 2 1) := by group
        _ = (short P hp 0 a)⁻¹ * (short P hp 2 1 * (short P hp 0 a * (armsCoordinates P hp v).val)) := congrArg _ h
        _ = _ := by group
    · calc
        _ = short P hp 0 a * ((armsCoordinates P hp v).val * short P hp 2 1) := by group
        _ = short P hp 0 a * (((short P hp 0 a)⁻¹ * short P hp 2 1 * short P hp 0 a) * (armsCoordinates P hp v).val) := congrArg _ h
        _ = _ := by group
  rw [he]
  have hsh : shearParameters P a (sparam P) = (![0,1],![0,armsPairing P a 1,0]) := by
    simp [shearParameters,sparam,higherCoefficient,-fieldFrobenius_apply]
  rw [hsh]
  constructor
  · intro h
    have h1 := congrArg (fun w : ArmsParameters P => w.2 1) h
    have h2 := congrArg (fun w : ArmsParameters P => w.2 2) h
    have ha : armsPairing P a 1=0 := by
      simpa [armsMultiply,armsCocycle,sparam] using h1.symm
    refine ⟨ha,?_⟩
    simpa [armsMultiply,armsCocycle,sparam,ha] using h2
  · rintro ⟨ha,hc⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [armsMultiply,sparam,add_comm]
    · funext i
      fin_cases i <;> simp [armsMultiply,armsCocycle,sparam,ha,hc,add_comm]

private theorem trace_kernel_card (P : Parameters) (hp : P.prime=2) :
    Nat.card (cubicTrace P).ker = P.q^2 := by
  have hh := (cubicTrace P).ker.card_mul_index
  rw [AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr (cubicTrace_surjective P hp),
    AddSubgroup.card_top,card_fixedField,card_extensionField] at hh
  apply Nat.eq_of_mul_eq_mul_right (by have := P.q_ge_two; omega : 0<P.q)
  simpa only [pow_succ] using hh

private def tailParameters (n : ℕ) (hn : 0<n) (v : PositiveParameters n hn) :
    ArmsParameters (binaryParameters n hn) := (![v.1 1,v.1 2],v.2)

private theorem baseProduct_tail (n : ℕ) (hn : 0<n) (v : PositiveParameters n hn) :
    baseProduct n hn v = short (binaryParameters n hn) rfl 0 (v.1 0) *
      (armsCoordinates (binaryParameters n hn) rfl (tailParameters n hn v)).val := by
  rw [armsCoordinates_factorization (binaryParameters n hn) rfl]
  simp only [tailParameters,baseProduct,Matrix.cons_val_zero,Matrix.cons_val_one,mul_assoc]

/-- The two independent cubic traces determine commutation in the full positive subgroup. -/
theorem baseProduct_commutes_iff (n : ℕ) (hn : 0<n) (v : PositiveParameters n hn) :
    baseProduct n hn v * short (binaryParameters n hn) rfl 2 1 =
      short (binaryParameters n hn) rfl 2 1 * baseProduct n hn v ↔
    cubicTrace (binaryParameters n hn) (v.1 0)=0 ∧
      cubicTrace (binaryParameters n hn) (v.1 1)=0 := by
  rw [baseProduct_tail,commutes_iff (binaryParameters n hn) rfl]
  simp only [tailParameters,Matrix.cons_val_zero,armsPairing,map_one,mul_one]

/-- The marked short-root centralizer in the genuine positive subgroup has order q^10. -/
theorem short_positive_centralizer_card (n : ℕ) (hn : 0<n) :
    let P := binaryParameters n hn
    Nat.card (unipotent P ⊓ centralizer ({short P rfl 2 1} : Set (Carrier P)) :
      Subgroup (Carrier P)) = P.q^10 := by
  let P := binaryParameters n hn
  let C := unipotent P ⊓ centralizer ({short P rfl 2 1} : Set (Carrier P))
  let X := (cubicTrace P).ker × (cubicTrace P).ker × ExtensionField P × (Fin 3 → fixedField P)
  let pack (x : X) : PositiveParameters n hn := (![x.1.val,x.2.1.val,x.2.2.1],x.2.2.2)
  let f : X → C := fun x => ⟨baseProduct n hn (pack x),
    (show baseProduct n hn (pack x) ∈ unipotent P from
      (positiveEquiv_val n hn (pack x)) ▸ (positiveEquiv n hn (pack x)).property),
    mem_centralizer_singleton_iff.mpr ((baseProduct_commutes_iff n hn (pack x)).mpr
      ⟨x.1.property,x.2.1.property⟩)⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh := baseProduct_injective n hn (congrArg Subtype.val he)
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun v : PositiveParameters n hn => v.1 0) hh)
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun v : PositiveParameters n hn => v.1 1) hh)
      · apply Prod.ext
        · exact congrArg (fun v : PositiveParameters n hn => v.1 2) hh
        · exact congrArg (fun v : PositiveParameters n hn => v.2) hh
  have hsurj : Function.Surjective f := by
    intro u
    obtain ⟨v,hv⟩ := (positiveEquiv n hn).surjective ⟨u.val,u.property.1⟩
    have hval : baseProduct n hn v=u.val :=
      (positiveEquiv_val n hn v).symm.trans (congrArg Subtype.val hv)
    have hc : cubicTrace P (v.1 0)=0 ∧ cubicTrace P (v.1 1)=0 :=
      (baseProduct_commutes_iff n hn v).mp (hval.symm ▸
        mem_centralizer_singleton_iff.mp u.property.2)
    refine ⟨(⟨v.1 0,hc.1⟩,⟨v.1 1,hc.2⟩,v.1 2,v.2),Subtype.ext ?_⟩
    change baseProduct n hn (pack _) = u.val
    rw [←hval]
    congr 1
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  change Nat.card C=P.q^10
  rw [←Nat.card_congr (Equiv.ofBijective f ⟨hf,hsurj⟩)]
  simp only [X,Nat.card_prod,Nat.card_fun,Nat.card_fin,trace_kernel_card P rfl,
    card_extensionField,card_fixedField]
  ring

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortSylow

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The exact q¹⁰ short-root centralizer count through the original right map. -/
theorem Preparation.triality_short_source_centralizer_card
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let v : G := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card (sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G) = P.q^10 := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  exact (triality_centralizer_card_transport P f hf _
    (d.triality_right_unipotent_image h hTH P rfl e)
    (TrialityCompletionFusion.shortElement P rfl)).trans
      (TrialityShortSylow.short_positive_centralizer_card m hm)

/-- Both marked root centralizers in the original ambient Sylow, with S=T
discharged from the source hypotheses and the same whole-overlap comparison. -/
theorem Preparation.triality_marked_sylow_centralizer_card
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let z : G := (e.right.symm (TrialityCompletionFusion.longElement P rfl)).val
    let v : G := (e.right.symm (TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card ((T : Subgroup G) ⊓ centralizer ({z} : Set G) : Subgroup G) = P.q^12 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Subgroup G) = P.q^10 := by
  have hST := d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)
  rw [← hST]
  exact ⟨(d.triality_marked_source_centralizer_bounds h hH.1.1.2 m hm e).1,
    d.triality_short_source_centralizer_card h hH.1.1.2 m hm e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
