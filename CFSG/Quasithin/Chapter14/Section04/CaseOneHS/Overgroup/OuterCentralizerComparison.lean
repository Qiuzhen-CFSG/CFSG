module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterSylowCentralizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.TransferredCentralizer
public import Theory.Frattini.Intersection

/-!
# The characteristic-point obstruction to matching Sylow centralizers

The upper central-Frattini bound for C_T(r) and the lower bound for
C_T(rᵍ) force any matching conjugator to normalize V₁. It therefore lies
in the original H, preserves Q=O₂(H), and contradicts Q intersect PU=U.
The argument retains the actual conjugator and both ambient centralizers.
The subsequent extremal-representative and transfer argument is still needed
to exclude the order-eight branch.

Source: Aschbacher--Smith, 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual transfer conjugator cannot carry the whole original Sylow
centralizer onto the target one. Such a map would preserve V₁, force the
conjugator into H, and contradict Q intersect PU=U. -/
theorem outer_involution_no_centralizer_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V)
    (g : G) (hg : g⁻¹*r*g ∈ L.pCoreIn 2 ⊔ F.U) (hgU : g⁻¹*r*g ∉ F.U) :
    conjugate ((T : Subgroup G) ⊓ centralizer ({r} : Set G)) g ≠
      (T : Subgroup G) ⊓ centralizer ({g⁻¹*r*g} : Set G) := by
  let C := (T : Subgroup G) ⊓ centralizer ({r} : Set G)
  let D := (T : Subgroup G) ⊓ centralizer ({g⁻¹*r*g} : Set G)
  intro hconj
  change conjugate C g = D at hconj
  have hphi : (frattini (conjugate C g)).map (conjugate C g).subtype =
      conjugate ((frattini C).map C.subtype) g :=
    frattini_image_map C (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hmark : conjugate (Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype) g =
      Chapter12.Section08.centerIn D ⊓ (frattini D).map D.subtype := by
    rw [conjugate_inf,←centerIn_conjugate,←hphi,hconj]
  have hpoint : F.Vi 1 ≤ conjugate (F.Vi 1) g := by
    have hupper := map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom)
      (outer_involution_central_frattini_le_point h structural alternatives F s hne
        x hx hx3 hcard r hr hrL hr2 hdis)
    change conjugate (Chapter12.Section08.centerIn C ⊓ (frattini C).map C.subtype) g ≤
      conjugate (F.Vi 1) g at hupper
    rw [hmark] at hupper
    exact (core_closure_point_le_central_frattini h structural alternatives F s hne _ hg).trans hupper
  have he : conjugate (F.Vi 1) g = F.Vi 1 :=
    (eq_of_le_of_card_ge hpoint (by rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective])).symm
  have hgH : g ∈ F.H := (conjugate_eq_iff (F.Vi 1) g).mp he
  have hn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hyQ : g⁻¹*r*g ∈ F.H.pCoreIn 2 := by
    have hh := (mem_normalizer_iff.mp (hn (F.H.inv_mem hgH)) r).mp hr.1
    simpa only [inv_inv] using hh
  exact hgU (core_closure_inter_point_core h structural alternatives F s hne ▸ ⟨hg,hyQ⟩)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
