module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.ResidualGeneration
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Residual generation in the full odd central cover of J₄

Pull back the native Sylow-compatible Mathieu subgroup through the specified
central quotient. Its perfect residual maps onto the native residual.
Odd-kernel lifting makes the literal involution-centralizer residual map
onto its native counterpart. Their join therefore covers the model; a
central supplement cannot enlarge a subgroup of a perfect group, so the
join is the entire covering group. The covering kernel is retained.

The preimage is invariant under every automorphism preserving the chosen
Sylow subgroup. The involution is required to centralize that actual Sylow;
being an arbitrary involution is not substituted for this condition.

Source: Aschbacher--Smith 4.4.3, the equality K = ⟨L_B,K_Z⟩ on printed p.623.
The separate source identification of L_B with this Mathieu residual is
not asserted here.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

/-- The residual generation identity lifts to the full odd central cover. -/
theorem exists_sylow_mathieu_residual_seed_of_odd_central_cover
    (e : (X ⧸ center X) ≃* Model) (hZ : Nat.Coprime 2 (Nat.card (center X)))
    (P : Sylow 2 X) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
    ∃ R : Subgroup Model, Nonempty (R ≃* SylowCore.Local) ∧
      (P : Subgroup X) ≤ R.comap q ∧
      (∀ b : MulAut X, (P : Subgroup X).map b.toMonoidHom = P →
        (R.comap q).map b.toMonoidHom = R.comap q) ∧
      ∀ z : X, orderOf z = 2 → z ∈ centralizer (P : Set X) →
        (solvableResidual (R.comap q)).map (R.comap q).subtype ⊔
          (solvableResidual (centralizer ({z} : Set X))).map
            (centralizer ({z} : Set X)).subtype = ⊤ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have ho : Nat.Coprime 2 (Nat.card q.ker) := hk.symm ▸ hZ
  let : Group.IsPerfect Model := Group.IsPerfect.ofSurjective (f := q) hq
  let Q := P.mapSurjective hq
  obtain ⟨R,hQR,he,hi,hgen⟩ := exists_sylow_mathieu_residual_seed Q
  refine ⟨R,he,(fun x hx => hQR (mem_map_of_mem q hx)),?_,?_⟩
  · intro b hb
    let bc := MulAut.centralQuotientAction e b
    have heqb (x : X) : q (b x) = bc (q x) := (MulAut.centralQuotientAction_apply e b x).symm
    have hQ : (Q : Subgroup Model).map bc.toMonoidHom = Q := by
      change ((P : Subgroup X).map q).map bc.toMonoidHom = (P : Subgroup X).map q
      rw [map_map]
      have he : bc.toMonoidHom.comp q = q.comp b.toMonoidHom := by ext x; exact (heqb x).symm
      rw [he,←map_map,hb]
    have hR := hi bc hQ
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change q (b x) ∈ R
      rw [heqb,←hR]
      exact mem_map_of_mem _ hx
    · exact (Nat.card_congr (b.subgroupMap (R.comap q)).toEquiv).le
  · intro z hz hc
    have hzq := orderOf_map_involution_of_odd_kernel q ho hz
    have hcq : q z ∈ centralizer (Q : Set Model) := by
      rintro y ⟨x,hx,rfl⟩
      simpa only [map_mul] using congrArg q (hc x hx)
    have hC := q.elementCentralizerMap_surjective_of_odd_kernel hq ho z hz
    have hmC : ((solvableResidual (centralizer ({z} : Set X))).map
        (centralizer ({z} : Set X)).subtype).map q =
        (solvableResidual (centralizer ({q z} : Set Model))).map
          (centralizer ({q z} : Set Model)).subtype := by
      have hh := congrArg (Subgroup.map (centralizer ({q z} : Set Model)).subtype)
        (map_solvableResidual_eq (q.elementCentralizerMap z) hC)
      have heq : (centralizer ({q z} : Set Model)).subtype.comp (q.elementCentralizerMap z) =
          q.comp (centralizer ({z} : Set X)).subtype := by ext x; rfl
      simpa only [map_map,heq] using hh
    let U := (solvableResidual (R.comap q)).map (R.comap q).subtype ⊔
      (solvableResidual (centralizer ({z} : Set X))).map
        (centralizer ({z} : Set X)).subtype
    have hm : U.map q = ⊤ := by
      rw [Subgroup.map_sup,map_solvableResidual_comap q hq R,hmC]
      exact hgen (q z) hzq hcq
    have hu : U ⊔ center X = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hm
      rwa [comap_map_eq,hk,comap_top] at hh
    exact eq_top_of_sup_center_eq_top U hu

end Janko4.LocalStructure
