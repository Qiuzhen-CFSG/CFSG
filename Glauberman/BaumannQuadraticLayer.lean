module
public import Glauberman.BaumannFixedIndex
public import Theory.GroupTheory.Commutator.NormalGeneration
public import Theory.GroupTheory.QuadraticNormalGeneration

/-!
# The all-abelian Baumann Sylow step from a quadratic residual layer

Let Z be the central omega of the ordinary Thompson subgroup of a Sylow P.
Suppose Baumann normally generates G, supplements O₂(G) in P, and has an
opposite conjugate generating modulo O₂(G). If ZD is elementary and normal,
D is residually generated, and P acts quadratically on D, then Baumann is P.

Quadratic normal generation centralizes D by O₂(G). The two opposite
commutator subgroups span D and lie in the corresponding Thompson central
omegas. The abelian supplement argument therefore centralizes Z by O₂(G)
and proves the Sylow equality. No fixed-index bounds or vanishing central
kernel are assumed. CriticalReduction.RootProductBaumannSylow supplies all
premises for the original closure and unchanged field degree.
Source: MS93 (5.1), printed p.913, the Baumann step before Niles.
-/

public noncomputable section
namespace Glauberman
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_commutator_sup (D A B : Subgroup G) [D.Normal] :
    ⁅D,A ⊔ B⁆ = ⁅D,A⁆ ⊔ ⁅D,B⁆ := by
  simpa only [iSup_bool_eq, Bool.false_eq_true, ↓reduceIte] using
    commutator_iSup_of_normal_left D (fun b : Bool => if b then A else B)

/-- Quadratic opposite generators finish the Sylow equality on the whole residual layer. -/
theorem baumann_eq_sylow_of_quadratic_residual_layer
    (S : Sylow 2 G) (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    [IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G)]
    [(omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G).Normal]
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤)
    (hsupp : baumannSubgroup (S : Subgroup G) ⊔ pCore 2 G = (S : Subgroup G))
    (hmoved : ⁅D,pResidual 2 G⁆ = D)
    (hquad : ⁅⁅D,(S : Subgroup G)⁆,(S : Subgroup G)⁆ = ⊥)
    (x : G)
    (hopp : (baumannSubgroup (S : Subgroup G) ⊔
      (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔ pCore 2 G = ⊤) :
    D ≤ centralizer (pCore 2 G : Set G) ∧
    pCore 2 G ≤ centralizer
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) : Set G) ∧
    baumannSubgroup (S : Subgroup G) = (S : Subgroup G) := by
  have hSgen : normalClosure (S : Set G) = ⊤ := top_unique
    (hgen.symm.le.trans (normalClosure_mono (show baumannSubgroup (S : Subgroup G) ≤
      (S : Subgroup G) from inf_le_left)))
  have hcore : D ≤ centralizer (pCore 2 G : Set G) :=
    hmoved.symm.le.trans ((commutator_mono le_rfl le_top).trans
      (core_centralizes_moved_of_quadratic_normal_generation D (pCore 2 G)
        (S : Subgroup G) (pCore_isPGroup.le_sylow_of_normal S) hSgen hquad))
  refine ⟨hcore,baumann_eq_sylow_of_residual_fixed_span S D hgen hsupp hcore x hopp ?_⟩
  let B := baumannSubgroup (S : Subgroup G)
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let f := (MulAut.conj x).toMonoidHom
  have hDmap : D.map f = D := Normal.map_conj_eq _ _
  have hDZ : ⁅D,B⁆ ≤ D ⊓ Z := by
    rw [←elementary_fixed_baumann S D]
    refine le_inf (commutator_le_left _ _) (commutator_eq_bot_iff_le_centralizer.mp ?_)
    exact bot_unique ((commutator_mono
      (commutator_mono le_rfl (show B ≤ (S : Subgroup G) from inf_le_left))
      (show B ≤ (S : Subgroup G) from inf_le_left)).trans_eq hquad)
  have hDZx : ⁅D,B.map f⁆ ≤ D ⊓ Z.map f := by
    have hh := map_mono (f := f) hDZ
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj x).injective,hDmap] at hh
  have hfull : ⁅D,(⊤ : Subgroup G)⁆ = D := le_antisymm
    (commutator_le_left _ _) (hmoved.symm.le.trans (commutator_mono le_rfl le_top))
  have hDC : ⁅D,pCore 2 G⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hcore
  calc
    D = ⁅D,(⊤ : Subgroup G)⁆ := hfull.symm
    _ = ⁅D,B⁆ ⊔ ⁅D,B.map f⁆ := by
      rw [←hopp,normal_commutator_sup,normal_commutator_sup,hDC,sup_bot_eq]
    _ ≤ (D ⊓ Z) ⊔ (D ⊓ Z.map f) := sup_le_sup hDZ hDZx
end Glauberman
