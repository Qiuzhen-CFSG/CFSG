module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Actors
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# From the local centralizing residual to the torus fixer

An automorphism preserving B preserves its two-core. Fixation of O³(B)
modulo that core therefore extends to O³(B)O₂(B), using the equalizer
of two quotient homomorphisms. If B normalizes an auxiliary C, then
B∩O₂(C)≤O₂(B). Hence O³(B)≤C and displacement of C into O₂(C)
supply the needed fixation without requiring C≤B.

An injective equivariant embedding transports the exact residual and
core conditions. Applying it to K*↪H* gives fixation by the original
marked actor from the local calculation in H*. This accommodates the
covered case B_C=O³(B)L₀ even when L₀ is not in B or K.
The required local containment and commutator statements remain explicit
premises; the small-commutator cardinality is a separate obligation.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
open TorusModels.Assembly
variable {D E : Type*} [Group D] [Group E] [Finite D]

/-- An injective equivariant embedding preserves the exact residual-torus
fixation condition, including its intrinsic two-core denominator. -/
theorem fixesTorus_map_iff_of_injective (f : D →* E) (hf : Function.Injective f)
    (B : Subgroup D) (a : MulAut D) (b : MulAut E)
    (heq : ∀ x, b (f x) = f (a x)) :
    FixesTorus (B.map f) b ↔ FixesTorus B a := by
  unfold FixesTorus residualIn
  rw [← map_embedded_pResidual, ← map_pCoreIn_of_injective 2 B f hf, ← Subgroup.map_sup]
  constructor
  · intro h x hx
    have hh := h (f x) (mem_map_of_mem f hx)
    rw [heq, ← map_inv, ← map_mul] at hh
    exact (mem_map_iff_mem hf).mp hh
  · rintro h _ ⟨x, hx, rfl⟩
    rw [heq, ← map_inv, ← map_mul]
    exact mem_map_of_mem f (h x hx)

omit [Finite D] in
/-- The core of an auxiliary group, intersected with a group normalizing it,
lies in that group's core. The auxiliary group need not lie in B. -/
private theorem core_intersection_le (B C : Subgroup D)
    (hBC : B ≤ normalizer (C : Set D)) : B ⊓ C.pCoreIn 2 ≤ B.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 C).to_le inf_le_right) inf_le_left
  exact (le_inf B.le_normalizer
    (hBC.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite D] in
/-- Fixation on O³(B) suffices once the actor preserves B. Its two-core is
preserved automatically and the equalizer is a subgroup of B. -/
theorem fixesTorus_of_residual_fixed (B : Subgroup D) (a : MulAut D)
    (hB : B.map a.toMonoidHom = B)
    (hR : ∀ x ∈ residualIn 3 B, a x * x⁻¹ ∈ B.pCoreIn 2) : FixesTorus B a := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let aB : B →* B := {
    toFun := fun x => ⟨a x, hB.le (mem_map_of_mem a.toMonoidHom x.property)⟩
    map_one' := by apply Subtype.ext; exact a.map_one
    map_mul' x y := by apply Subtype.ext; exact a.map_mul x y }
  let F := ((q.comp aB).eqLocus q).map B.subtype
  have hF (x : D) : x ∈ F ↔ x ∈ B ∧ a x * x⁻¹ ∈ B.pCoreIn 2 := by
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.property, ?_⟩
      have he : q (aB b) = q b := hb
      have hh := QuotientGroup.eq_iff_div_mem.mp he
      exact ⟨aB b / b, hh, by simp only [div_eq_mul_inv]; rfl⟩
    · rintro ⟨hx, y, hy, he⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      change q (aB ⟨x, hx⟩) = q ⟨x, hx⟩
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hy' : aB ⟨x, hx⟩ / ⟨x, hx⟩ = y := Subtype.ext (by simpa [aB, div_eq_mul_inv] using he.symm)
      rwa [hy']
  have hcore : (B.pCoreIn 2).map a.toMonoidHom = B.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 B a.toMonoidHom a.injective, hB]
  have hRF : residualIn 3 B ≤ F := fun x hx =>
    (hF x).mpr ⟨map_subtype_le _ hx, hR x hx⟩
  have hPF : B.pCoreIn 2 ≤ F := by
    intro x hx
    exact (hF x).mpr ⟨pCoreIn_le 2 B hx,
      (B.pCoreIn 2).mul_mem (hcore.le (mem_map_of_mem _ hx)) ((B.pCoreIn 2).inv_mem hx)⟩
  exact fun x hx => ((hF x).mp ((sup_le hRF hPF) hx)).2

omit [Finite D] in
/-- The source auxiliary centralizing residual supplies torus fixation.
This also applies when B_C contains the extra covered factor L₀ outside B. -/
theorem fixesTorus_of_centralizing_residual (B C : Subgroup D) (a : MulAut D)
    (hB : B.map a.toMonoidHom = B) (hBC : B ≤ normalizer (C : Set D))
    (hR : residualIn 3 B ≤ C)
    (hC : ∀ x ∈ C, a x * x⁻¹ ∈ C.pCoreIn 2) : FixesTorus B a := by
  apply fixesTorus_of_residual_fixed B a hB
  intro x hx
  have hxB : x ∈ B := map_subtype_le _ hx
  exact core_intersection_le B C hBC
    ⟨B.mul_mem (hB.le (mem_map_of_mem _ hxB)) (B.inv_mem hxB), hC x (hR hx)⟩

/-- Stabilizing the specified Sylow stabilizes its normalizer and residual. -/
theorem residualAt_stable (S : Sylow 2 D) (a : MulAut D)
    (hS : (S : Subgroup D).map a.toMonoidHom = S) :
    (residualAt S).map a.toMonoidHom = residualAt S := by
  change (borelResidual (normalizer (S : Set D))).map a.toMonoidHom = _
  rw [show (borelResidual (normalizer (S : Set D))).map a.toMonoidHom =
    borelResidual ((normalizer (S : Set D)).map a.toMonoidHom) from
      map_embedded_pResidual 2 _ _]
  have hn : (normalizer (S : Set D)).map a.toMonoidHom = normalizer (S : Set D) := by
    have hh := (S : Subgroup D).map_normalizer_eq_of_bijective (f := a.toMonoidHom) a.bijective
    rw [hS] at hh
    exact hh
  rw [hn]

/-- A local auxiliary centralizer in H* gives fixation by the prescribed
actor on the intrinsic Borel of K*. C may be the star image of B_C; it is
not required to lie in K*. All kernel and core denominators are retained. -/
theorem markedActor_fixes_of_centralizer
    (H K T : Subgroup D) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (t : H) (ht : t.val ∈ T) (C : Subgroup (Source.Hstar H))
    (hBC : Source.starImage H (borel H K T hKH hT) ≤ normalizer (C : Set (Source.Hstar H)))
    (hR : residualIn 3 (Source.starImage H (borel H K T hKH hT)) ≤ C)
    (hC : ∀ x ∈ C, QuotientGroup.mk' (pCore 2 H) t * x *
      (QuotientGroup.mk' (pCore 2 H) t)⁻¹ * x⁻¹ ∈ C.pCoreIn 2) :
    FixesTorus (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht) := by
  let f := (Source.starImage H K).subtype
  let a := markedActor H K T t ht
  let b := MulAut.conj (QuotientGroup.mk' (pCore 2 H) t)
  let B := residualAt (sourceSylow H K T hT)
  have heq (x : Source.starImage H K) : b (f x) = f (a x) := rfl
  have hBa : B.map a.toMonoidHom = B :=
    residualAt_stable _ _ (starActor_stable H K T hT _)
  have hmap : (B.map f).map b.toMonoidHom = (B.map a.toMonoidHom).map f := by
    rw [map_map, map_map]
    exact congrArg (fun m => B.map m) (MonoidHom.ext heq)
  have hstar : B.map f = Source.starImage H (borel H K T hKH hT) :=
    (borel_star_intrinsic H K T hKH hT).symm
  have hstable : (Source.starImage H (borel H K T hKH hT)).map b.toMonoidHom =
      Source.starImage H (borel H K T hKH hT) := by
    rw [← hstar, hmap, hBa]
  apply (fixesTorus_map_iff_of_injective f (Source.starImage H K).subtype_injective B a b heq).mp
  rw [hstar]
  exact fixesTorus_of_centralizing_residual _ C b hstable hBC hR hC

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel

end
