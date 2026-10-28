module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.PathCoreControl

/-!
# Odd fixers of the strict seven-path

In the strict branch of DGS (10.10), append a nonreturning edge to the
Cartan six-path `g • y -- g • u -- t -- α -- β -- u -- y`.
A two-subgroup fixing the resulting seven-path lies in every interior
two-core.  The Cartan residual's trivial intersection with `Q_y` therefore
forces that two-subgroup to be trivial.  Cauchy's theorem gives odd order
for the full path stabilizer.

Source: DGS, *Groups and Graphs* (1985), (10.10), printed p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The literal seven-path has odd fixer once its interior residual vanishes
at `y`.  Only the interior-core consequence of strict noncommutation is used. -/
theorem original_bTwo_seven_path_fixer_odd_of_residual
    (h : HypothesisF11 L S) {u t y z : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (g : G₀ L S) (p : BasedWalk (graph F) 7 (g • y))
    (hp : p.Nonbacktracking)
    (hv : p.vertices = [g • y,g • u,t,α,β,u,y,z])
    (hzero : ((D F β t ⊓ Q F u) ⊓ Q F (g • u)) ⊓ Q F y = ⊥) :
    Odd (Nat.card (pathStabilizer F p)) := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let P := pathStabilizer F p
  let : Finite P := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hd
  let A := zpowers (x : G₀ L S)
  have hpA : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    change Nat.card (zpowers (x : G₀ L S)) ∣ 2^1
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]
    decide)
  have hAP : A ≤ P := zpowers_le.mpr x.property
  have hcores : ∀ z ∈ p.2.vertices.dropLast, A ≤ Q F z :=
    original_noncommuting_path_two_subgroup_core h hc hne (r := 5) p hp A hpA hAP
  have htail : p.2.vertices = [g • u,t,α,β,u,y,z] := by
    have ht := congrArg List.tail hv
    simpa only [BasedWalk.vertices,List.tail_cons] using ht
  have hAgu : A ≤ Q F (g • u) := hcores _ (by rw [htail]; simp)
  have hAt : A ≤ Q F t := hcores _ (by rw [htail]; simp)
  have hAβ : A ≤ Q F β := hcores _ (by rw [htail]; simp)
  have hAu : A ≤ Q F u := hcores _ (by rw [htail]; simp)
  have hAy : A ≤ Q F y := hcores _ (by rw [htail]; simp)
  have hA : A = ⊥ := bot_unique
    ((le_inf (le_inf (le_inf (le_inf hAβ hAt) hAu) hAgu) hAy).trans hzero.le)
  have hx1 : x = 1 := Subtype.ext (mem_bot.mp (hA ▸ mem_zpowers (x : G₀ L S)))
  simp only [hx1,orderOf_one] at hx
  omega

/-- The original strict Cartan construction gives odd fixers for every
nonreturning terminal extension of its explicit six-path. -/
theorem original_bTwo_seven_path_fixer_odd
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g : G₀ L S, g ∈ graphLocalGroup F α ∧ g • β = t ∧
      ∀ z : Vertex F, (graph F).Adj y z → z ≠ u →
        ∃ p : BasedWalk (graph F) 7 (g • y),
          p.vertices = [g • y,g • u,t,α,β,u,y,z] ∧
          p.Nonbacktracking ∧ Odd (Nat.card (pathStabilizer F p)) := by
  obtain ⟨K,hfix,hd,hgen,hoK,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  refine ⟨g,hg,hgt,?_⟩
  intro z hyz hzu
  have hgygu : (graph F).Adj (g • y) (g • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hy.symm
  have hgut : (graph F).Adj (g • u) t := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rw [hgt] at hh
    exact hh.symm
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let p : BasedWalk (graph F) 7 (g • y) :=
    ⟨⟨g • u,hgygu⟩,⟨⟨t,hgut⟩,⟨⟨α,ht.symm⟩,⟨⟨β,hab⟩,
      ⟨⟨u,hβu⟩,⟨⟨y,hy⟩,⟨⟨z,hyz⟩,PUnit.unit⟩⟩⟩⟩⟩⟩⟩
  have hua : u ≠ α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    omega
  have hgyt : g • y ≠ t := by
    intro he
    apply hyne
    apply MulAction.injective g
    exact he.trans hgt.symm
  have hguα : g • u ≠ α := by
    intro he
    apply hua
    apply MulAction.injective g
    exact he.trans (sylowGenerated_le _ hg).symm
  have hp : p.Nonbacktracking :=
    ⟨hgyt.symm,hguα.symm,htne.symm,hua,hyne,hzu,True.intro⟩
  refine ⟨p,rfl,hp,?_⟩
  apply original_bTwo_seven_path_fixer_odd_of_residual h (t := t) (z := z) hc hne g p hp rfl
  rw [← hR]
  exact hzero

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
