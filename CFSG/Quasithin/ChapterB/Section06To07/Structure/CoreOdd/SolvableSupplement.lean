module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import Theory.GroupTheory.TwoCoreOddSylowSupplement
public import Theory.Frattini.Intersection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Frattini intersection for the odd Sylow supplement of a solvable parabolic

Let M be the unique maximal overgroup of T, J its normal core, and P a
Sylow subgroup for the odd prime in B.6.8(2). The quotient map modulo O₂(H)
is injective on P. Transporting B.6.8's Frattini identity through this map
gives Φ(P) = P ∩ J. In H/J, the odd residual is disjoint from the image of
M, so P ∩ M = P ∩ J. Thus the Frattini identity holds on the actual P.

Source: Aschbacher–Smith, B.6.8(2), printed pp.113–114, and the construction
preceding 12.2.20, printed p.802.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterB
open Subgroup
variable {H : Type*} [Group H] [Finite H]

theorem minimalParabolic_odd_sylow_frattini_intersection
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H))
    (hPhi : minimalParabolicCoreImage T hP =
      Stellmacher.frattiniAmbient (pCore p (H ⧸ pCore 2 H))) (P : Sylow p H) :
    (frattini P).map (P : Subgroup H).subtype = (P : Subgroup H) ⊓ minimalParabolicMax T hP := by
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let J := minimalParabolicCore T hP
  have hQJ : Q ≤ J := minimalParabolicTwoCore_le_core T hP
  have hi := quotient_twoCore_injective_on_odd_sylow ho P
  let e : P ≃* (P : Subgroup H).map q := MulEquiv.ofBijective
    (q.subgroupMap (P : Subgroup H)) ⟨fun x y he => hi (congrArg Subtype.val he),
      q.subgroupMap_surjective _⟩
  have hphiMap : ((frattini P).map (P : Subgroup H).subtype).map q = J.map q := by
    change _ = minimalParabolicCoreImage T hP
    rw [hPhi]
    change _ = (frattini (pCore p (H ⧸ Q))).map (pCore p (H ⧸ Q)).subtype
    rw [← sylow_map_twoCoreQuotient_eq_odd_core ho hr P, ← frattini_map_equiv e, map_map, map_map]
    rfl
  have hPJ : (frattini P).map (P : Subgroup H).subtype = (P : Subgroup H) ⊓ J := by
    apply le_antisymm
    · refine le_inf (map_subtype_le _) ?_
      have hm := map_le_iff_le_comap.mp hphiMap.le
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_eq_left.mpr hQJ] using hm
    · intro x hx
      obtain ⟨y, hy, he⟩ := hphiMap.symm ▸ mem_map_of_mem q hx.2
      have hxy : (⟨y, map_subtype_le _ hy⟩ : P) = ⟨x, hx.1⟩ := hi he
      have heq : y = x := congrArg Subtype.val hxy
      exact heq ▸ hy
  rw [hPJ]
  have hJM : J ≤ minimalParabolicMax T hP := normalCore_le _
  apply le_antisymm (inf_le_inf_left _ hJM)
  intro x hx
  refine ⟨hx.1, ?_⟩
  let qJ := QuotientGroup.mk' J
  obtain ⟨_, _, _, _, _, hd⟩ := minimalParabolic_solvable_star_structure T hP hs
  have hxR : qJ x ∈ pResidual 2 (H ⧸ J) :=
    odd_prime_subgroup_le_twoResidual ho ((P : Subgroup H).map qJ)
      (P.isPGroup'.map qJ) (mem_map_of_mem qJ hx.1)
  have hxM := mem_map_of_mem qJ hx.2
  have he : qJ x ∈ (⊥ : Subgroup (H ⧸ J)) := hd ▸ (show qJ x ∈ pResidual 2 (H ⧸ J) ⊓
    (minimalParabolicMax T hP).map qJ from ⟨hxR, hxM⟩)
  exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp he)

end CFSG.Quasithin.ChapterB
