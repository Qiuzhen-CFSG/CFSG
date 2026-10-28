module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceTransport
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.AdaptedPair
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers

/-!
# The corrected H.9 adapted-pair theorem on the source module

The coordinate theorem now has all action, index and stabilizer-order inputs
discharged. The constructed marked comparison transports its vector and actor
together to the original module and original Sylow. Residual and commutator
transport identify its geometric complement with the actual [V,L_v].

Source: the adequate replacement for H.9.1(4), as specified in the source
audit of 6 October 2026, and its uses in 12.1.1 and 12.1.3. The pure-vector
Sylow marking of H.9.1(3) is not imposed on this nonsingular vector.
-/

public section
open BinaryNaturalDual BinaryNaturalDual.AdaptedPair BinaryNaturalDual.ModelOrbits
open BinaryNaturalDual.VectorStabilizers Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual

/-- All ordinary index and stabilizer-order premises of the coordinate
adapted-pair theorem are consequences of the actual model. -/
theorem coordinate_adapted_pair {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (v : CoordinateSpace n) (hv : BinaryNaturalDual.quadratic v = 1)
    (A : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)))
    (hA : IsPGroup 2 A) (hAv : A ≤ pointStabilizer (linearAction d) v) :
    ∃ l ∈ innerGroup n, ∃ v' : CoordinateSpace n,
      v' = linearAction d l v ∧ BinaryNaturalDual.quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (pointStabilizer (linearAction d) v'),
        (Q : Subgroup _).map (pointStabilizer (linearAction d) v').subtype =
          (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') ∧
      A.map (MulAut.conj l).toMonoidHom ≤
        (T : Subgroup _) ⊓ pointStabilizer (linearAction d) v' ∧
      movingSpace v' ⊓ fixedVectors (linearAction d)
        ((T : Subgroup _) ⊓ pointStabilizer (linearAction d) v') =
          fixedVectors (linearAction d) T ∧
      Module.finrank (ZMod 2) (fixedVectors (linearAction d) T) = 1 ∧
      ∃ a ∈ innerGroup n, linearAction d a v' = v' ∧
        ∃ z ∈ fixedVectors (linearAction d) T, linearAction d a z ≠ z := by
  have hi : (innerGroup n).index = 2 := AutomorphismModel.inner_index hn
  rcases hn with rfl | rfl
  · apply adapted_pair_four d hi ?_ T v hv A hA hAv
    have he : pointStabilizer (linearAction d) vectorFour = fullStabilizer d vectorFour := by
      ext a; rfl
    rw [he]
    exact fullStabilizer_card_four d (x := vectorFour.1) (f := vectorFour.2)
      quadratic_vectorFour
  · apply adapted_pair_five d hi ?_ T v hv A hA hAv
    have he : pointStabilizer (linearAction d) vectorFive = fullStabilizer d vectorFive := by
      ext a; rfl
    rw [he]
    exact fullStabilizer_card_five d (x := vectorFive.1) (f := vectorFive.2)
      quadratic_vectorFive

namespace SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- The corrected source adapted-pair theorem. The same layer element moves
the nonsingular vector and its supplied two-subgroup into the original Sylow.
Its Sylow centralizer has exactly the required fixed line on [V,L_v], and
L_v moves that line. There is no model, order, orbit or adapted-witness premise. -/
theorem adapted_pair (T : Sylow 2 M) (v : V) (hv : S.quadratic v = 1)
    (A : Subgroup M) (hA : IsPGroup 2 A) (hAv : A ≤ S.stabilizer v) :
    ∃ l ∈ componentLayer M, ∃ v' : V,
      v' = S.representation l v ∧ S.quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (S.stabilizer v'),
        (Q : Subgroup _).map (S.stabilizer v').subtype =
          (T : Subgroup M) ⊓ S.stabilizer v') ∧
      A.map (MulAut.conj l).toMonoidHom ≤ (T : Subgroup M) ⊓ S.stabilizer v' ∧
      S.moving v' ⊓ S.fixed ((T : Subgroup M) ⊓ S.stabilizer v') = S.fixed T ∧
      Module.finrank (ZMod 2) (S.fixed T) = 1 ∧
      ∃ a ∈ S.residual v', ∃ z ∈ S.fixed T, S.representation a z ≠ z := by
  let := S.finite_group
  let d := AutomorphismModel.coordinateAction S.degree
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) := Finite.of_injective
    (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
      (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
    DFunLike.coe_injective
  let e := S.model.group
  let E := S.model.coordinates
  have hact (g : M) (u : V) : E (S.representation g u) = d.representation (e g) (E u) :=
    S.model.equivariant g u
  have hL (g : M) : e g ∈ innerGroup n ↔ g ∈ componentLayer M := S.model.inner_iff g
  have hv' : BinaryNaturalDual.quadratic (E v) = 1 := (S.quadratic_apply v).symm.trans hv
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hAv' : A.map e.toMonoidHom ≤ pointStabilizer (linearAction d) (E v) := by
    rintro _ ⟨a,ha,rfl⟩
    change d.representation (e a) (E v) = E v
    rw [← hact, hAv ha]
  obtain ⟨l,hl,w,hw,hqw,⟨P,hP⟩,hAP,hfixed,hdim,⟨a,ha,hav,z,hz,haz⟩⟩ :=
    coordinate_adapted_pair S.degree d T' (E v) hv' (A.map e.toMonoidHom)
      (hA.map _) hAv'
  let l₀ := e.symm l
  let w₀ := E.symm w
  have hw₀ : E w₀ = w := E.apply_symm_apply w
  have hqw₀ : S.quadratic w₀ = 1 := by rw [S.quadratic_apply, hw₀]; exact hqw
  have hgroup : e l₀ = l := e.apply_symm_apply l
  have hstab : (S.stabilizer w₀).map e.toMonoidHom = pointStabilizer (linearAction d) w := by
    rw [S.stabilizer_map, hw₀]
    ext b; rfl
  have hinter : ((T : Subgroup M) ⊓ S.stabilizer w₀).map e.toMonoidHom =
      (T' : Subgroup _) ⊓ pointStabilizer (linearAction d) w := by
    rw [Subgroup.map_inf _ _ _ e.injective, hstab]
    rfl
  have hfixedT : (S.fixed T).map E.toLinearMap = fixedVectors (linearAction d) T' :=
    S.fixed_map_adapted T
  refine ⟨l₀, (hL l₀).mp (by rw [hgroup]; exact hl), w₀,
    ?_, hqw₀, ?_, ?_, ?_, ?_, ?_⟩
  · apply E.injective
    rw [hact, hgroup, hw₀]
    exact hw
  · have heq : pointStabilizer (linearAction d) w =
        representationStabilizer d.representation (E w₀) := by rw [hw₀]; ext b; rfl
    let P' : Sylow 2 (representationStabilizer d.representation (E w₀)) :=
      P.mapSurjective (f := (MulEquiv.subgroupCongr heq).toMonoidHom)
        (MulEquiv.subgroupCongr heq).surjective
    apply Transport.sylow_stabilizer_pullback S.representation d.representation e E
      hact T w₀ P'
    have hemb : (P' : Subgroup _).map
        (representationStabilizer d.representation (E w₀)).subtype =
        (P : Subgroup _).map (pointStabilizer (linearAction d) w).subtype := by
      change ((P : Subgroup (pointStabilizer (linearAction d) w)).map
        (MulEquiv.subgroupCongr heq).toMonoidHom).map
        (representationStabilizer d.representation (E w₀)).subtype = _
      rw [Subgroup.map_map]
      rfl
    rw [hemb, hP, ← heq]
    rfl
  · rintro b ⟨c,hc,rfl⟩
    have hm : e (MulAut.conj l₀ c) ∈
        ((T : Subgroup M) ⊓ S.stabilizer w₀).map e.toMonoidHom := by
      rw [hinter]
      have he : e (MulAut.conj l₀ c) = MulAut.conj l (e c) := by
        simp only [MulAut.conj_apply, map_mul, map_inv, hgroup]
      rw [he]
      exact hAP (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hc))
    obtain ⟨b,hb,he⟩ := hm
    exact e.injective he ▸ hb
  · apply Submodule.map_injective_of_injective (f := E.toLinearMap) E.injective
    rw [Submodule.map_inf _ E.injective, S.moving_map_nonsingular hqw₀,
      S.fixed_map_adapted, hinter, hw₀, hfixedT]
    exact hfixed
  · have he := (Submodule.equivMapOfInjective E.toLinearMap E.injective (S.fixed T)).finrank_eq
    rw [hfixedT] at he
    exact he.trans hdim
  · refine ⟨e.symm a, ?_, E.symm z, ?_, ?_⟩
    · rw [S.residual_eq_innerStabilizer hqw₀]
      refine ⟨(hL _).mp ?_, ?_⟩
      · simpa only [e.apply_symm_apply] using ha
      · apply E.injective
        rw [hact, e.apply_symm_apply, hw₀]
        exact hav
    · have hz' : z ∈ (S.fixed T).map E.toLinearMap := by rw [hfixedT]; exact hz
      obtain ⟨z₀,hz₀,he⟩ := hz'
      have he' : E.symm z = z₀ := by rw [← he]; exact E.symm_apply_apply z₀
      exact he' ▸ hz₀
    · intro h
      apply haz
      have he := congrArg E h
      change E (S.representation (e.symm a) (E.symm z)) = E (E.symm z) at he
      rw [hact, e.apply_symm_apply, E.apply_symm_apply] at he
      exact he

/-- The trivial-actor specialization used to begin source 12.1.1. -/
theorem adapted_vector (T : Sylow 2 M) (v : V) (hv : S.quadratic v = 1) :
    ∃ l ∈ componentLayer M, ∃ v' : V,
      v' = S.representation l v ∧ S.quadratic v' = 1 ∧
      (∃ Q : Sylow 2 (S.stabilizer v'),
        (Q : Subgroup _).map (S.stabilizer v').subtype =
          (T : Subgroup M) ⊓ S.stabilizer v') ∧
      S.moving v' ⊓ S.fixed ((T : Subgroup M) ⊓ S.stabilizer v') = S.fixed T ∧
      Module.finrank (ZMod 2) (S.fixed T) = 1 ∧
      ∃ a ∈ S.residual v', ∃ z ∈ S.fixed T, S.representation a z ≠ z := by
  obtain ⟨l,hl,v',hv',hq,hP,_,hfix,hdim,hmoves⟩ :=
    S.adapted_pair T v hv ⊥ (IsPGroup.of_subsingleton 2 _) bot_le
  exact ⟨l,hl,v',hv',hq,hP,hfix,hdim,hmoves⟩

end SourceSetup
end CFSG.Quasithin.ChapterH.NaturalDual
