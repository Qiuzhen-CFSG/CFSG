module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.Geometry

/-!
# Field complements inside binary hyperplanes

A binary hyperplane contains a unique largest field subspace, of field
codimension one. If it supplements a field line, that subspace complements
the line. Pulling an original binary complement back through a surjection
then produces a field complement whose image is exactly the original
subspace and on which the surjection is injective.

The largest-subspace characterization transfers stabilizers through the same
map, for both linear and semilinear actions. The original nonsplit Sp₄ cover
application is in `OrthogonalComplements`.

Source: Aschbacher--Smith, proof of 11.2.2, printed p.767. The remaining
orthogonal orbit and local-centralizer arguments stay with
qt-d-1222-natural-weak-parameters.
-/

public noncomputable section
open Representation Submodule
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
section Linear
variable {F X W : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module F X] [Module (ZMod 2) X] [IsScalarTower (ZMod 2) F X]
  [FiniteDimensional F X] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite F] in
theorem field_subspace_le_of_binary_hyperplane
    (B : Submodule (ZMod 2) X) (hB : B ≠ ⊤)
    (Q : Submodule F X) (hQ : Module.finrank F Q + 1 = Module.finrank F X)
    (hQB : Q.restrictScalars (ZMod 2) ≤ B)
    (P : Submodule F X) (hPB : P.restrictScalars (ZMod 2) ≤ B) : P ≤ Q := by
  have hsup : Q ⊔ P ≠ ⊤ := by
    intro he
    apply hB
    apply top_unique
    intro x _
    have hx : x ∈ Q ⊔ P := he.symm ▸ mem_top
    obtain ⟨q,hq,p,hp,rfl⟩ := Submodule.mem_sup.mp hx
    exact B.add_mem (hQB hq) (hPB hp)
  have hd := Submodule.finrank_lt hsup
  have he : Q = Q ⊔ P := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  rw [he]
  exact le_sup_right

theorem field_complement_in_binary_hyperplane
    (B : Submodule (ZMod 2) X)
    (hB : Module.finrank (ZMod 2) B + 1 = Module.finrank (ZMod 2) X)
    (R : Submodule F X) (hR : Module.finrank F R = 1)
    (hRB : ¬ R.restrictScalars (ZMod 2) ≤ B) :
    ∃ Q : Submodule F X, Module.finrank F Q + 1 = Module.finrank F X ∧
      Q.restrictScalars (ZMod 2) ≤ B ∧ IsCompl Q R ∧
      ∀ P : Submodule F X, P.restrictScalars (ZMod 2) ≤ B → P ≤ Q := by
  obtain ⟨Q,hQ,hQB⟩ := field_hyperplane_in_binary (F := F) B hB
  have hneq : B ≠ ⊤ := by intro he; rw [he, finrank_top] at hB; omega
  have hRQ : ¬ R ≤ Q := fun h => hRB (fun _ hx => hQB (h hx))
  have hi : Q ⊓ R = ⊥ := by
    apply (Submodule.finrank_eq_zero (R := F)).mp
    have hle := Submodule.finrank_mono (inf_le_right : Q ⊓ R ≤ R)
    have hn : Module.finrank F (Q ⊓ R : Submodule F X) ≠ 1 := by
      intro hd
      have he : Q ⊓ R = R := Submodule.eq_of_le_of_finrank_eq inf_le_right (hd.trans hR.symm)
      exact hRQ (he ▸ (inf_le_left : Q ⊓ R ≤ Q))
    omega
  have hs : Q ⊔ R = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hd := Submodule.finrank_sup_add_finrank_inf_eq Q R
    rw [hi, finrank_bot, hR] at hd
    omega
  exact ⟨Q,hQ,hQB,⟨disjoint_iff.mpr hi,codisjoint_iff.mpr hs⟩,
    field_subspace_le_of_binary_hyperplane B hneq Q hQ hQB⟩

theorem binary_hyperplane_comap [FiniteDimensional (ZMod 2) X]
    (f : X →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (U : Submodule (ZMod 2) W)
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) W) :
    Module.finrank (ZMod 2) (U.comap f) + 1 = Module.finrank (ZMod 2) X := by
  let q := U.mkQ.comp f
  have hq : Function.Surjective q := U.mkQ_surjective.comp hf
  have hk : q.ker = U.comap f := by simp only [q, LinearMap.ker_comp, ker_mkQ]
  have hd := LinearMap.finrank_range_add_finrank_ker q
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, hk] at hd
  have hu := U.finrank_quotient_add_finrank
  omega
end Linear


section Images
variable {F X W : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module F X] [Module (ZMod 2) X] [IsScalarTower (ZMod 2) F X]
  [FiniteDimensional F X] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem field_complement_image
    (f : X →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (U : Submodule (ZMod 2) W)
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) W)
    (R : Submodule F X) (hR : Module.finrank F R = 1)
    (hcompl : IsCompl U ((R.restrictScalars (ZMod 2)).map f))
    (hker : f.ker ≤ R.restrictScalars (ZMod 2)) :
    ∃ Q : Submodule F X, Module.finrank F Q + 1 = Module.finrank F X ∧
      IsCompl Q R ∧ (Q.restrictScalars (ZMod 2)).map f = U ∧
      Disjoint (Q.restrictScalars (ZMod 2)) f.ker ∧
      ∀ P : Submodule F X, (P.restrictScalars (ZMod 2)).map f ≤ U → P ≤ Q := by
  let : Finite X := Module.finite_of_finite F
  have hneq : U ≠ ⊤ := by intro he; rw [he, finrank_top] at hU; omega
  have hRB : ¬ R.restrictScalars (ZMod 2) ≤ U.comap f := by
    intro h
    have hm := Submodule.map_le_iff_le_comap.mpr h
    have hz : (R.restrictScalars (ZMod 2)).map f = ⊥ :=
      le_bot_iff.mp (by simpa only [hcompl.disjoint.eq_bot] using (le_inf hm le_rfl))
    have he := hcompl.codisjoint.eq_top
    rw [hz, sup_bot_eq] at he
    exact hneq he
  obtain ⟨Q,hQ,hQB,hQR,hgreat⟩ := field_complement_in_binary_hyperplane
    (U.comap f) (binary_hyperplane_comap f hf U hU) R hR hRB
  have hQU : (Q.restrictScalars (ZMod 2)).map f ≤ U :=
    Submodule.map_le_iff_le_comap.mpr hQB
  have he : (Q.restrictScalars (ZMod 2)).map f = U := by
    apply le_antisymm hQU
    intro u hu
    obtain ⟨x,rfl⟩ := hf u
    have hx : x ∈ Q ⊔ R := hQR.codisjoint.eq_top.symm ▸ mem_top
    obtain ⟨q,hq,r,hr,hx⟩ := Submodule.mem_sup.mp hx
    have hfr : f r ∈ U := by
      have hsum : f q + f r = f x := by rw [←map_add,hx]
      exact (U.add_mem_iff_right (hQB hq)).mp (hsum.symm ▸ hu)
    have hz : f r = 0 := hcompl.disjoint.eq_bot.le ⟨hfr,⟨r,hr,rfl⟩⟩
    refine ⟨q,hq,?_⟩
    rw [←hx,map_add,hz,add_zero]
  refine ⟨Q,hQ,hQR,he,?_,fun P hP => hgreat P (Submodule.map_le_iff_le_comap.mp hP)⟩
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  exact hQR.disjoint.eq_bot.le ⟨hx.1,hker hx.2⟩

omit [Finite F] [FiniteDimensional (ZMod 2) W] in
theorem field_complement_stabilizer
    (f : X →ₗ[ZMod 2] W) (Q : Submodule F X) (U : Submodule (ZMod 2) W)
    (him : (Q.restrictScalars (ZMod 2)).map f = U)
    (hgreat : ∀ P : Submodule F X, (P.restrictScalars (ZMod 2)).map f ≤ U → P ≤ Q)
    (a : X ≃ₗ[F] X) (b : W ≃ₗ[ZMod 2] W)
    (hab : ∀ x, f (a x) = b (f x)) :
    Q.map a.toLinearMap = Q ↔ U.map b.toLinearMap = U := by
  have him' : ((Q.map a.toLinearMap).restrictScalars (ZMod 2)).map f =
      U.map b.toLinearMap := by
    rw [restrictScalars_map, ←Submodule.map_comp, ←him, ←Submodule.map_comp]
    congr 1
    exact LinearMap.ext hab
  constructor
  · intro h
    rw [←him',h,him]
  · intro h
    have hle := hgreat (Q.map a.toLinearMap) (by rw [him',h])
    exact Submodule.eq_of_le_of_finrank_eq hle (a.finrank_map_eq Q)
omit [FiniteDimensional (ZMod 2) W] in
theorem field_complement_semilinear_stabilizer
    (f : X →ₗ[ZMod 2] W) (Q : Submodule F X) (U : Submodule (ZMod 2) W)
    (him : (Q.restrictScalars (ZMod 2)).map f = U)
    (hgreat : ∀ P : Submodule F X, (P.restrictScalars (ZMod 2)).map f ≤ U → P ≤ Q)
    (σ τ : F →+* F) [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    (a : LinearEquiv σ (σ' := τ) X X)
    (b : W ≃ₗ[ZMod 2] W)
    (hab : ∀ x, f (a x) = b (f x)) :
    Q.map a.toLinearMap = Q ↔ U.map b.toLinearMap = U := by
  have him' : ((Q.map a.toLinearMap).restrictScalars (ZMod 2)).map f =
      U.map b.toLinearMap := by
    ext w
    constructor
    · rintro ⟨x,⟨q,hq,rfl⟩,rfl⟩
      exact ⟨f q,him ▸ ⟨q,hq,rfl⟩,(hab q).symm⟩
    · rintro ⟨y,hy,rfl⟩
      rw [←him] at hy
      obtain ⟨x,hx,rfl⟩ := hy
      exact ⟨a x,⟨x,hx,rfl⟩,hab x⟩
  constructor
  · intro h
    rw [←him',h,him]
  · intro h
    have hle := hgreat (Q.map a.toLinearMap) (by rw [him',h])
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hc := Nat.card_congr (Q.equivMapOfInjective a.toLinearMap a.injective).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := F) (V := Q),
      Module.natCard_eq_pow_finrank (K := F) (V := Q.map a.toLinearMap)] at hc
    exact Nat.pow_right_injective (Finite.one_lt_card (α := F)) hc.symm
end Images

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
