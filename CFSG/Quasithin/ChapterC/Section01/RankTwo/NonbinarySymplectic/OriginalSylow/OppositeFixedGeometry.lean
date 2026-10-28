module
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane

/-!
# Natural fixed vectors of a full symplectic Sylow subgroup

A Sylow two-subgroup is symplectically conjugate to the standard unipotent
subgroup, whose fixed space is its distinguished point. Its fixed space is
therefore isotropic and lies in its natural displacement space.

This is the natural-module input for eliminating the opposite fixed-core
intersection in the Sylow case of MS93 (3.7), printed p.877.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow

variable {E : Type*} [Field E] [Finite E]

/-- Every fixed vector of a full Sylow two-subgroup lies in its natural
displacement space. The actual Sylow subgroup and natural action are retained. -/
theorem sylow_fixedSpace_le_displacementSpace {n : ℕ}
    (hE : Nat.card E = 2^n) (hn : 0 < n) (S : Sylow 2 (Sp E)) :
    TwoLocalCover.fixedSpace (S : Subgroup (Sp E)) ≤
      displacementSpace (S : Subgroup (Sp E)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E) S (unipotentSylow hE hn)
  have hS : (S : Subgroup (Sp E)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun T : Sylow 2 (Sp E) => (T : Subgroup (Sp E))) hg
  have hfixed (v : Vector E) (hv : v ∈ TwoLocalCover.fixedSpace (S : Subgroup (Sp E))) :
      g • v ∈ point E := by
    apply (fixedBy_unipotent_iff _).mp
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hS.symm ▸ hx
    change (g*y*g⁻¹) • (g • v) = g • v
    simp only [mul_smul,inv_smul_smul,hv y hy]
  have hiso (x : Vector E) (hx : x ∈ TwoLocalCover.fixedSpace (S : Subgroup (Sp E)))
      (y : Vector E) (hy : y ∈ TwoLocalCover.fixedSpace (S : Subgroup (Sp E))) :
      form E x y = 0 := by
    rw [←preserves_form g x y]
    exact point_isotropic _ _ (hfixed x hx) (hfixed y hy)
  intro v hv
  have hp : v ∈ (form E).orthogonal (TwoLocalCover.fixedSpace (S : Subgroup (Sp E))) :=
    fun w hw => hiso w hw v hv
  rwa [←orthogonal_displacementSpace,LinearMap.BilinForm.orthogonal_orthogonal
    TwoLocalCover.form_nondegenerate TwoLocalCover.form_alternating.isRefl] at hp

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
