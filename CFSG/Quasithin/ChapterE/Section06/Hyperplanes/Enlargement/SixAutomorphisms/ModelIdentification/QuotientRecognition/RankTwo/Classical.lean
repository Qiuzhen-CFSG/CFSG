module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.FieldRecognition
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.SymplecticInner
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.SymplecticGraph
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical.Linear
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
/-!
# Classical rank-two fixed-component inspection

The inner symplectic branch is excluded by the actual parabolic Levi maps.
The odd graph-field branch is excluded by the concrete Suzuki fixed-group
identification. In the field branch, the unique fixed component and the
symplectic order formula force field order four, retaining a genuine ambient
isomorphism that intertwines the specified involution.

The theorem below assembles these branches with the existing normal-form
reduction. Semilinear coverage and the two cocycle descents remain explicit
outstanding inputs. The linear branch is reduced to the genuine residual models from its
involution table. The unconditional classical inspection remains owned by
this module; these conditional reductions are not the completed source result.

Source: Aschbacher–Smith, Theorem C and A.2.4, printed p.33; E.6.8,
pp.247–248; E.6.23, p.254; 16.1.4, pp.1170–1172.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
universe u

private theorem map_fixed_le {D H : Type*} [Group D] [Group H]
    (e : D ≃* H) (a : MulAut D) (S : Subgroup D) (hS : S ≤ a.fixedSubgroup) :
    S.map e.toMonoidHom ≤ (MulAut.congr e a).fixedSubgroup := by
  rintro x ⟨y, hy, rfl⟩
  rw [MulAut.mem_fixedSubgroup]
  change e (a (e.symm (e y))) = e y
  rw [e.symm_apply_apply, (MulAut.mem_fixedSubgroup a y).mp (hS hy)]

/-- All symplectic component comparisons are discharged; only automorphism
coverage and genuine matrix cocycle descent remain as premises. -/
theorem symplecticInspection_of_semilinear_and_descent
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ a : MulAut (Sp F), PreservesDiagram a →
        ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hfield : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ n : ℕ, 1 < n → Nat.card F = 2 ^ n → Even n → ∀ g : Sp F,
        g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
        ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (hgraph : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ n : ℕ, 1 < n → Nat.card F = 2 ^ n → Odd n → ∀ g : Sp F,
        g * (graphAut ^ n) g = 1 → ∃ h : Sp F, g = h * ((graphAut ^ n) h)⁻¹) :
    SymplecticInspection.{u} := by
  intro D _ _ _ _ f hf hm a ha S hS hSix
  obtain ⟨F, hField, hFinite, hF, ⟨e0⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let e : D ≃* Sp F := e0.trans EvenProjective.equiv.symm
  have hao : orderOf (MulAut.congr e a) = 2 := (MulAut.congr e).orderOf_eq a |>.trans ha
  rcases InvolutionNormalForms.involution_normalForms_of_coboundaries hF (by omega)
    (hclass F) (hfield F f (by omega) hF) (hgraph F f (by omega) hF)
    (MulAut.congr e a) hao with hi | ⟨heven, hc⟩ | ⟨hodd, hc⟩
  · obtain ⟨g, hg, he⟩ := hi
    have hs := map_fixed_le e a S hS.1
    rw [he] at hs
    exact (not_six_inner g hg _ hs
      (hSix.map (fun s => (e.subgroupMap S).symm.trans s))).elim
  · obtain ⟨d, hd⟩ := exists_compatible_of_isConj e a _ hc
    have hmul : 2 * (f / 2) = f := Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
    have hn : 1 ≤ f / 2 := by omega
    have hcard : Nat.card F = 2 ^ (2 * (f / 2)) := by rw [hmul]; exact hF
    have hr := field_recognition hn hcard d a hd S hS hSix
    exact ⟨F, hField, hFinite, inferInstance, hr.1, d, hr.2⟩
  · obtain ⟨m, hm⟩ := hodd
    have hf' : f = 2 * m + 1 := hm
    have hmpos : 0 < m := by omega
    obtain ⟨d, hd⟩ := exists_compatible_of_isConj e a _ hc
    have hs := map_fixed_le d a S hS.1
    rw [hd, hf'] at hs
    exact (not_six_graph hmpos (hf' ▸ hF) _ hs
      (hSix.map (fun s => (d.subgroupMap S).symm.trans s))).elim

/-- The exact linear inspection follows from the genuine fixed two-residual
table. The table itself remains an outstanding classification input. -/
theorem linearInspection_of_residual_models
    (hrows : ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
      ∀ f : ℕ, 1 ≤ f → ClassicalGroup.IsPSL D 3 (2 ^ f) →
      ∀ a : MulAut D, orderOf a = 2 → LinearResidualModels a.fixedSubgroup) :
    LinearInspection.{u} := by
  intro D _ _ _ _ f hf hD a ha S hS
  exact not_six_component_of_residual_models a (hrows D f hf hD a ha) S hS

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
