module
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.Quotient


/-!
# Residual two-cores and their odd local quotients

Under the genuine Section Seven hypotheses, let `d,l` be adjacent vertices
and let `L ≤ G_d` be arbitrary. Then the two-core of the two-residual of
`L` is contained in the actual vertex core `Q_d`. The quotient of this
two-residual by its own two-core has odd order.

The edge data supplies a solvable local-family member `G_d`. Applying
(3.3)(a) directly to this local group gives an odd-prime-power two-residual
in its ordinary quotient by `O₂(G_d)`. The image of `O²(L)` lies in this
residual: compose its quotient map with the further two-group quotient and
use the defining minimal property of the two-residual on the kernel.
Consequently the two-core of `O²(L)` has an image which is both a two-group
and of odd order. This image is trivial, so pulling back through the
ordinary quotient places the original two-core in `Q_d`. Conversely, the
kernel of the restricted quotient map is a normal two-subgroup, since it
is the inverse image of `O₂(G_d)` under an injective subgroup inclusion.
It therefore equals the residual's two-core. The first isomorphism theorem
identifies the quotient by that core with the odd-order image. Both public
results project from this shared argument.

These supply the upper containment in the second configuration of assertion
(6) and the odd quotient used in assertion (7) of Stellmacher (8.4), Journal of Algebra 190 (1997), printed p.39.
No containment of `Q_d` in `L`, normality of `L`, or extra
characteristic-two hypothesis is needed.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext BenderSuzuki.External

private theorem local_residual_core_data
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (L : Subgroup G) (hLP : L ≤ stabilizer Γ d) :
    twoCoreIn (twoResidualIn L) ≤ q Γ d ∧
      Odd (Nat.card (twoResidualIn L ⧸ pCore 2 (twoResidualIn L))) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := stabilizer Γ d
  let T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l) := default
  let W := sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T
  obtain ⟨h3, hP, _, hsolv, _, _⟩ := edge_sectionThree_data h Γ hl T
  obtain ⟨M, hM, hWM, huniq⟩ := hP.2
  have hWP : W ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    change (U : Subgroup P).map P.subtype = W at hU
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hMdata : IsCoatom M ∧ W.subgroupOf P ≤ M ∧
      ∀ M' : Subgroup P, IsCoatom M' → W.subgroupOf P ≤ M' → M' = M := by
    refine ⟨hM, ?_, ?_⟩
    · intro t ht
      obtain ⟨m, hm, he⟩ := hWM ht
      exact P.subtype_injective he ▸ hm
    · intro M' hM' hW'
      apply huniq M' hM'
      intro t ht
      exact ⟨⟨t, hWP ht⟩, hW' ht, rfl⟩
  obtain ⟨p, hp, hpodd, hres⟩ :=
    (SectionThree.lemma_three_three W h3 P hP M M.normalCore hMdata
      ⟨M.normalCore_le, inferInstance, fun N hN hNM => by
        let _ := hN
        exact Subgroup.normal_le_normalCore.mpr hNM⟩ hsolv).part_a
  let π := QuotientGroup.mk' (pCore 2 P)
  let Rbar := hktPResidual 2 (P ⧸ pCore 2 P)
  have : Rbar.Normal := hktPResidual_normal
  have hodd : Odd (Nat.card Rbar) := by
    have hh : IsPGroup p Rbar := by
      rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hres
      exact hres
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hh.exists_card_eq
    rw [hn]
    exact hpodd.pow
  let f : L →* (P ⧸ pCore 2 P) := π.comp (Subgroup.inclusion hLP)
  let k := (QuotientGroup.mk' Rbar).comp f
  have hkquot : IsPGroup 2 (L ⧸ k.ker) := by
    have hpgroup := hktPResidual_quotient_isPGroup (q := 2) (Q := P ⧸ pCore 2 P)
    exact (hpgroup.to_subgroup k.range).of_equiv (QuotientGroup.quotientKerEquivRange k).symm
  have hresker : twoResidualSubgroup L ≤ k.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact hktPResidual_le k.ker inferInstance hkquot
  let R := twoResidualIn L
  have hRL : R ≤ L := Subgroup.map_subtype_le _
  let fR : R →* (P ⧸ pCore 2 P) := π.comp (Subgroup.inclusion (hRL.trans hLP))
  have hfR : fR.range ≤ Rbar := by
    rintro _ ⟨r, rfl⟩
    obtain ⟨a, ha, hea⟩ := r.property
    have hk : k a = 1 := hresker ha
    have hrbar : f a ∈ Rbar := (QuotientGroup.eq_one_iff _).mp hk
    have he : f a = fR r := by
      apply congrArg π
      apply Subtype.ext
      exact hea
    exact he ▸ hrbar
  have hmaple : (pCore 2 R).map fR ≤ Rbar :=
    (Subgroup.map_le_range fR _).trans hfR
  have hpmap := (pCore_isPGroup (p := 2) (G := R)).map fR
  have hmapbot : (pCore 2 R).map fR = ⊥ := by
    rcases hpmap.card_eq_or_dvd with hcard | hdvd
    · exact Subgroup.card_eq_one.mp hcard
    · exact False.elim ((Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
        (hdvd.trans (Subgroup.card_dvd_of_le hmaple))))
  have hcoreker : pCore 2 R ≤ fR.ker := (Subgroup.map_eq_bot_iff _).mp hmapbot
  have hkerTwo : IsPGroup 2 fR.ker := by
    dsimp only [fR]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := P)).comap_of_injective
      (Subgroup.inclusion (hRL.trans hLP)) (Subgroup.inclusion_injective _)
  have hkerEq : fR.ker = pCore 2 R :=
    le_antisymm (le_sSup ⟨inferInstance, hkerTwo⟩) hcoreker
  have hoddRange : Odd (Nat.card fR.range) :=
    Nat.coprime_two_left.mp
      (hodd.coprime_two_left.of_dvd_right (Subgroup.card_dvd_of_le hfR))
  have hcard : Nat.card (R ⧸ pCore 2 R) = Nat.card fR.range := by
    rw [← hkerEq]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange fR).toEquiv
  refine ⟨?_, hcard ▸ hoddRange⟩
  rintro a ⟨r, hr, rfl⟩
  have hπ : π (Subgroup.inclusion (hRL.trans hLP) r) = 1 := hcoreker hr
  have hcore := (QuotientGroup.eq_one_iff _).mp hπ
  rw [q, Γ.twoCoreAt_def]
  exact Subgroup.mem_map_of_mem P.subtype hcore

/-- The two-core of a subgroup's two-residual lies in the local vertex core. -/
public theorem local_residual_core_le_vertex_core
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (L : Subgroup G) (hLP : L ≤ stabilizer Γ d) :
    twoCoreIn (twoResidualIn L) ≤ q Γ d :=
  (local_residual_core_data h Γ d l hl L hLP).1

/-- The two-residual of any subgroup of a local vertex stabilizer has odd
order modulo its own two-core. -/
public theorem local_residual_core_quotient_odd
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (L : Subgroup G) (hLP : L ≤ stabilizer Γ d) :
    Odd (Nat.card (twoResidualIn L ⧸ pCore 2 (twoResidualIn L))) :=
  (local_residual_core_data h Γ d l hl L hLP).2

end Stellmacher.SectionsFiveToSeven
