module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Contracts
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointGeometry

/-!
# Ambient placement of the standard local subgroups

The aligned flag makes T normalize the four Vᵢ and their literal residuals
Lᵢ = N_L(Vᵢ)∞. The first-node parabolic contains T and lies in M₁.
These are the placement inputs for the source C-component argument;
C-component membership and ambient normalizer containment remain separate.
The imported point geometry supplies |V₁| = 2 and G₁ = C_G(z).

Source: Aschbacher--Smith, notation before 12.5.2--3, printed p.817.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace ExteriorMarking
variable (a : ExteriorMarking D)

theorem Li_le (i : ℕ) : a.Li i ≤ L ⊓ a.Gi i := map_subtype_le _
theorem Li_le_L (i : ℕ) : a.Li i ≤ L := (a.Li_le i).trans inf_le_left
theorem Li_le_Gi (i : ℕ) : a.Li i ≤ a.Gi i := (a.Li_le i).trans inf_le_right
end ExteriorMarking

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The extended actor contains the entire original component quotient. -/
theorem actor_surjective : Function.Surjective s.actor := by
  intro g
  obtain ⟨q, rfl⟩ := s.marking.quotientEquiv.surjective g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩,
    s.actor_component l⟩

theorem sylow_le_Gi (i : ℕ) (hi : LocalIndex i) : (T : Subgroup G) ≤ s.marking.Gi i := by
  obtain ⟨h₁, h₃, h₄, h₆, _⟩ := Representation.SL5ExteriorSquare.flagGroup_stabilizes_standard
  rcases hi with rfl | rfl | rfl | rfl
  · exact s.sylow_normalizes_subspace _ h₁
  · exact s.sylow_normalizes_subspace _ h₃
  · exact s.sylow_normalizes_subspace _ h₄
  · exact s.sylow_normalizes_subspace _ h₆

theorem sylow_normalizes_Li (i : ℕ) (hi : LocalIndex i) :
    (T : Subgroup G) ≤ normalizer (s.marking.Li i : Set G) := by
  have hn : (T : Subgroup G) ≤ normalizer (L ⊓ s.marking.Gi i : Set G) :=
    (le_inf D.sylow_normalizes_component
      ((s.sylow_le_Gi i hi).trans (s.marking.Gi i).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ s.marking.Gi i) (solvableResidual (L ⊓ s.marking.Gi i : Subgroup G)))

theorem Li_join_sylow_le_Gi (i : ℕ) (hi : LocalIndex i) :
    s.marking.Li i ⊔ (T : Subgroup G) ≤ s.marking.Gi i :=
  sup_le (s.marking.Li_le_Gi i) (s.sylow_le_Gi i hi)

theorem sylow_le_P : (T : Subgroup G) ≤ s.P := by
  intro t ht
  refine ⟨⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) ht⟩, ?_, rfl⟩
  apply mem_iInf.mpr
  intro k
  apply mem_iInf.mpr
  intro _
  exact Representation.SL5ExteriorSquare.flagGroup_le_parabolic k.val k.isLt
    (s.sylow_flag ⟨t, ht⟩)

theorem P_le_M₁ : s.P ≤ s.marking.Mi 1 := by
  rintro x ⟨h, hh, rfl⟩
  refine ⟨h.property, ?_⟩
  apply mem_normalizer_iff.mpr
  intro v
  have hpar : s.actor h ∈ Representation.SL5ExteriorSquare.parabolic 2 :=
    mem_iInf.mp (mem_iInf.mp hh (2 : Fin 5)) (by decide)
  have hstab := Representation.SL5ExteriorSquare.parabolic_two_le_stabilizer_V₁ hpar
  constructor
  · intro hv
    have hvV := s.marking.subspace_le _ hv
    have he := s.equivariant h ⟨v, hvV⟩
    apply (s.marking.mem_subspace _ ⟨(h : G) * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalizes h.property) v).mp hvV⟩).mpr
    rw [he]
    exact (hstab _).mpr ((s.marking.mem_subspace _ ⟨v, hvV⟩).mp hv)
  · intro hv
    have hvV : v ∈ V :=
      (mem_normalizer_iff.mp (s.normalizes h.property) v).mpr
        (s.marking.subspace_le _ hv)
    have he := s.equivariant h ⟨v, hvV⟩
    apply (s.marking.mem_subspace _ ⟨v, hvV⟩).mpr
    apply (hstab _).mp
    have hh := (s.marking.mem_subspace _ ⟨(h : G) * v * (h : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalizes h.property) v).mp hvV⟩).mp hv
    rwa [he] at hh

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
