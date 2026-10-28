module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
/-!
# Putting an odd subgroup into a prescribed Hall subgroup by a Sylow element

Hall containment and conjugacy in a solvable overgroup give a conjugator.
Factor it as a Sylow-two element times an element of the prescribed odd Hall
subgroup; the latter preserves that Hall subgroup. The remaining conjugator
therefore lies in the original Sylow. Source application: Aschbacher--Smith
10.2.3(4), pp.746--747, retaining the prescribed Hall and component geometry.
-/
public section
open Subgroup
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]
theorem exists_sylow_conjugate_le_hall
    (T : Sylow 2 G) (M A B : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hAM : A ≤ M)
    (hsolv : Group.IsSolvable M) (hA : Odd (Nat.card A))
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf M)) :
    ∃ t ∈ (T : Subgroup G), A.map (MulAut.conj t).toMonoidHom ≤ B := by
  obtain ⟨D,hAD,hDM,hD⟩ := exists_hall_containing_odd M A hsolv hAM hA
  obtain ⟨g,hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hB hD
  obtain ⟨⟨t,b⟩,htb⟩ := (sylow_complement_of_hall (T.subtype hTM) hB).2 g
  refine ⟨(t.val:G)⁻¹,(T : Subgroup G).inv_mem t.property,?_⟩
  rintro _ ⟨a,ha,rfl⟩
  have haD : (⟨a,hAM ha⟩ : M) ∈ D.subgroupOf M := hAD ha
  rw [hg] at haD
  obtain ⟨x,hx,he⟩ := haD
  have heG := congrArg (fun x : M => (x:G)) he
  have htG := congrArg (fun x : M => (x:G)) htb
  change (t.val:G)*(b.val:G)=(g:G) at htG
  change (g:G)*(x:G)*(g:G)⁻¹=a at heG
  have hb : (b.val:G) ∈ B := b.property
  have hxB : (x:G) ∈ B := hx
  change (t.val:G)⁻¹*a*((t.val:G)⁻¹)⁻¹ ∈ B
  rw [←heG,←htG]
  have hh := B.mul_mem (B.mul_mem hb hxB) (B.inv_mem hb)
  convert hh using 1
  group
end Subgroup.OddHall
