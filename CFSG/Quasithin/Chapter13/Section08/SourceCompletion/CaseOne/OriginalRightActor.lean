module
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalMaps
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.LinearModels

/-!
# Aligning the original common cubic on the H-side

The ordinary natural-action kernel is a two-group, so the previously
lifted cubic has order three. Its star image is also faithful. Sylow
conjugacy inside the actual syntheme stabilizer aligns that image with
the published cubic, preserving the full parabolic and the whole module.
Only the H-side coordinates change; the subgroup in the ambient group
and the original L-side coordinates remain the same.

OriginalRightFiltration uses these maps to compare the two literal
filtrations. Both whole-module possibilities retain their constant kernel.
Source: Aschbacher--Smith, 13.8.33, printed p.968.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open ComponentSieve.SixAndG2.NaturalSix

/-- All order-three subgroups of the actual syntheme stabilizer are conjugate
inside that stabilizer to the published cubic actor. -/
theorem syntheme_cubic_alignment (B : Subgroup Symmetric) (hB : B ≤ H2)
    (hcard : Nat.card B = 3) :
    ∃ g : H2, B.map (MulAut.conj (g : Symmetric)).toMonoidHom = cubicActor := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl (D : Subgroup Symmetric) (hD : D ≤ H2) (hc : Nat.card D = 3) :
      ∃ S : Sylow 3 H2, (S : Subgroup H2) = D.subgroupOf H2 := by
    have hd : Nat.card (D.subgroupOf H2) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv).trans hc
    have hi : (D.subgroupOf H2).index = 16 := by
      have he := (D.subgroupOf H2).index_mul_card
      rw [hd,show Nat.card H2 = 48 from synthemeStabilizer_order] at he
      omega
    have hp : IsPGroup 3 (D.subgroupOf H2) := IsPGroup.of_card (n := 1) (by simpa using hd)
    exact ⟨hp.toSylow (by rw [hi]; decide),rfl⟩
  obtain ⟨S,hS⟩ := hsyl B hB hcard
  obtain ⟨R,hR⟩ := hsyl cubicActor cubicActor_le_H2 cubicActor_card
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H2 S R
  have he : (B.subgroupOf H2).map (MulAut.conj g).toMonoidHom = cubicActor.subgroupOf H2 := by
    rw [← hS,← hR]
    exact congrArg (fun P : Sylow 3 H2 => (P : Subgroup H2)) hg
  refine ⟨g,?_⟩
  have hm := congrArg (fun D : Subgroup H2 => D.map H2.subtype) he
  rw [map_subgroupOf_eq_of_le cubicActor_le_H2] at hm
  rw [map_map] at hm
  have hcomp : H2.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Symmetric)).toMonoidHom.comp H2.subtype := by ext x; rfl
  rw [hcomp,← map_map,map_subgroupOf_eq_of_le hB] at hm
  exact hm
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open A6Endgame.ActionAnalysis33.ChiefModels
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open A6Endgame.PointNormalizer
open ComponentSieve.SixAndG2.NaturalSix
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The cubic lifted through the original natural action really has order three;
the full action kernel is a two-group. -/
theorem original_cubic_card
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (A : Subgroup G) (hAL : A ≤ L ⊔ (T : Subgroup G)) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hm : ∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d)
      (inclusion hAL b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) :
    Nat.card A = 3 := by
  have hi : Function.Injective f := by
    apply (f.ker_eq_bot_iff).mp
    apply _root_.eq_bot_iff.mpr
    intro b hb
    have he : Section07.NaturalAction.permutation (localNaturalSetup d) (inclusion hAL b) = 1 := by
      rw [hm,show f b = 1 from hb,map_one]
      rfl
    have hk : inclusion hAL b ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
      rw [← ordinary_natural_kernel d h eL]
      exact he
    have hd := hA.disjoint_of_coprime (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) (by decide)
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hd b.property (mem_map_of_mem _ hk)
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hi,hf⟩).toEquiv).trans cubicActor_card

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem linear_coordinates_conjugate
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (coords : LinearCoordinates a e.toMonoidHom) (g : Equiv.Perm (Fin 6)) :
    LinearCoordinates a (e.trans (MulAut.conj g)).toMonoidHom := by
  rcases coords with ⟨F,hF⟩ | ⟨F,hF⟩
  · let r := BinaryPermutation.naturalRepresentation (Fin 6)
    refine Or.inl ⟨F.trans (LinearEquiv.ofBijective (r g) (r.apply_bijective g)),?_⟩
    intro b v
    change r g (F (tildeRepresentation H _ V₁ a b v)) =
      r (g * e b * g⁻¹) (r g (F v))
    rw [hF]
    change r g (r (e b) (F v)) = _
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  · let r := BinaryPermutation.coreRepresentation (Fin 6)
    refine Or.inr ⟨F.trans (LinearEquiv.ofBijective (r g) (r.apply_bijective g)),?_⟩
    intro b v
    change r g (F (tildeRepresentation H _ V₁ a b v)) =
      r (g * e b * g⁻¹) (r g (F v))
    rw [hF]
    change r g (r (e b) (F v)) = _
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

omit [Finite G] in
/-- Recoordinate the H-side within its original parabolic, preserving the same
actual cubic subgroup and the full whole-module action. -/
theorem exists_original_star_cubic_coordinates
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (coords : LinearCoordinates a e.toMonoidHom)
    (P : Subgroup G) (hPH : P ≤ H)
    (hpar : (Source.starImage H P).map e.toMonoidHom = H2)
    (A : Subgroup G) (hAP : A ≤ P) (hcard : Nat.card A = 3) :
    ∃ e' : Source.Hstar H ≃* Equiv.Perm (Fin 6),
      LinearCoordinates a e'.toMonoidHom ∧
      (Source.starImage H P).map e'.toMonoidHom = H2 ∧
      ∃ f : A →* cubicActor, Function.Surjective f ∧
        ∀ b : A, e' (QuotientGroup.mk' (pCore 2 H) (inclusion (hAP.trans hPH) b)) = (f b : Equiv.Perm (Fin 6)) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let φ : A →* Equiv.Perm (Fin 6) := q.comp (inclusion (hAP.trans hPH))
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hi : Function.Injective φ := by
    apply (φ.ker_eq_bot_iff).mp
    apply _root_.eq_bot_iff.mpr
    intro b hb
    have he : QuotientGroup.mk' (pCore 2 H) (inclusion (hAP.trans hPH) b) = 1 :=
      e.injective ((show e (QuotientGroup.mk' (pCore 2 H) (inclusion (hAP.trans hPH) b)) = 1 from hb).trans (map_one e).symm)
    have hk := (QuotientGroup.eq_one_iff (inclusion (hAP.trans hPH) b)).mp he
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp
      (hA.disjoint_of_coprime (isPGroup_pCoreIn 2 H) (by decide)) b.property (mem_map_of_mem _ hk)
  have hB : φ.range ≤ H2 := by
    rintro _ ⟨b,rfl⟩
    rw [← hpar]
    exact ⟨QuotientGroup.mk' (pCore 2 H) (inclusion (hAP.trans hPH) b),
      ⟨inclusion (hAP.trans hPH) b,hAP b.property,rfl⟩,rfl⟩
  have hBc : Nat.card φ.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hcard
  obtain ⟨g,hg⟩ := syntheme_cubic_alignment φ.range hB hBc
  let e' := e.trans (MulAut.conj (g : Equiv.Perm (Fin 6)))
  let ψ := (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom.comp φ
  have hr : ψ.range = cubicActor := by rw [MonoidHom.range_comp,hg]
  let f : A →* cubicActor := ψ.codRestrict cubicActor (fun b => hr ▸ (show ψ b ∈ ψ.range from ⟨b,rfl⟩))
  refine ⟨e',linear_coordinates_conjugate a e coords g,?_,f,?_,fun _ => rfl⟩
  · change (Source.starImage H P).map
      ((MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom.comp e.toMonoidHom) = H2
    rw [← map_map,hpar]
    exact mem_normalizer_iff_map_conj_eq.mp (H2.le_normalizer g.property)
  · rintro ⟨b,hb⟩
    obtain ⟨x,hx⟩ := hr.symm ▸ hb
    exact ⟨x,Subtype.ext hx⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
