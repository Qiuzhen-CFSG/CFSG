module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Cover
public import Mathlib.LinearAlgebra.Projection

/-!
# Removing a fixed supplement before identifying the cover

A central natural quotient need not make the whole original module a cover.
The commutator space has a fixed complement when commutators and fixed vectors
span. Projection along that complement is equivariant and is injective on
every displacement. The resulting moving module is a genuine cover.
-/

@[expose] public noncomputable section
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {k J W N : Type*} [Field k] [Group J]
    [AddCommGroup W] [Module k W] [AddCommGroup N] [Module k N]

/-- A fixed supplement gives an equivariant retraction onto the literal moved space. -/
theorem moving_cover_of_fixed_supplement
    (ρ : Representation k J W) (τ : Representation k J N)
    (p : ρ.IntertwiningMap τ) (hps : Function.Surjective p)
    (hpk : p.toLinearMap.ker = fixed ρ)
    (hs : Coinvariants.ker ρ ⊔ fixed ρ = ⊤) :
    ∃ (σ : Representation k J (Coinvariants.ker ρ))
      (q : ρ.IntertwiningMap σ) (pC : σ.IntertwiningMap τ),
      IsCover pC ∧
      (∀ w : Coinvariants.ker ρ, q w = w) ∧
      (∀ w, pC (q w) = p w) ∧
      Function.Surjective q ∧
      (∀ (A : Subgroup J),
        (Coinvariants.ker (ρ.comp A.subtype)).map q.toLinearMap =
          Coinvariants.ker (σ.comp A.subtype)) := by
  let C := Coinvariants.ker ρ
  obtain ⟨Z,hZ,hZC⟩ :=
    (show Codisjoint (fixed ρ) C from
      codisjoint_iff.mpr (by simpa only [sup_comm] using hs)).exists_isCompl
  have hCi : ∀ g, C ≤ C.comap (ρ g) := by
    intro g w hw
    change ρ g w ∈ C
    simpa only [sub_add_cancel] using C.add_mem (Coinvariants.sub_mem_ker g w) hw
  let σ := ρ.subrepresentation C hCi
  let q₀ := C.projectionOnto Z hZC.symm
  have hret (w : C) : q₀ w = w := Submodule.projectionOnto_apply_left hZC.symm w
  have hdisp (g : J) (w : W) :
      ρ g w - w = ρ g (q₀ w).val - (q₀ w).val := by
    have hz : w - (q₀ w).val ∈ Z := Submodule.sub_projection_mem hZC.symm w
    have he := hZ hz g
    rw [map_sub] at he
    calc
      _ = (ρ g w - ρ g (q₀ w).val) - (w - (q₀ w).val) +
          (ρ g (q₀ w).val - (q₀ w).val) := by abel
      _ = _ := by rw [he,sub_self,zero_add]
  let q : ρ.IntertwiningMap σ :=
    q₀.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g w
      apply Subtype.ext
      have hd := congrArg q₀ (hdisp g w)
      rw [map_sub,map_sub] at hd
      have hleft : q₀ (ρ g (q₀ w).val) = σ g (q₀ w) :=
        hret (σ g (q₀ w))
      rw [hleft,hret] at hd
      exact congrArg Subtype.val (sub_left_inj.mp hd))
  have hqsur : Function.Surjective q := Submodule.projectionOnto_surjective hZC.symm
  have hpq (w : W) : p (q w).val = p w := by
    have hz : w - (q w).val ∈ Z := Submodule.sub_projection_mem hZC.symm w
    have hh : w - (q w).val ∈ p.toLinearMap.ker := hpk.symm ▸ hZ hz
    change p (w - (q w).val) = 0 at hh
    rw [map_sub,sub_eq_zero] at hh
    exact hh.symm
  let pC : σ.IntertwiningMap τ :=
    (p.toLinearMap.comp C.subtype).intertwiningMap_of_isIntertwiningMap _ _
      (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w)
  have hpCsur : Function.Surjective pC := by
    intro v
    obtain ⟨w,rfl⟩ := hps v
    exact ⟨q w,hpq w⟩
  have hpCfixed : pC.toLinearMap.ker ≤ fixed σ := by
    intro w hw g
    apply Subtype.ext
    exact (hpk ▸ (show w.val ∈ p.toLinearMap.ker from hw)) g
  have hgen : Coinvariants.ker σ = ⊤ := by
    rw [← map_coinvariants_of_surjective q hqsur]
    apply top_unique
    intro w _
    exact ⟨w.val,w.property,hret w⟩
  refine ⟨σ,q,pC,⟨hpCsur,hpCfixed,hgen⟩,hret,hpq,hqsur,?_⟩
  intro A
  let qA : Representation.IntertwiningMap (ρ.comp A.subtype) (σ.comp A.subtype) :=
    q.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun g w => LinearMap.congr_fun (q.isIntertwining' g.val) w)
  exact map_coinvariants_of_surjective qA hqsur

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
