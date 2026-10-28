module

public import Stellmacher.SectionThree.LemmaThreeThree

/-!
# Core control for a normal subgroup of a solvable local group

Let `P ∈ PSet ⊤ S` be solvable and let `K ◁ P`. If `KS` is proper in
`P`, then `K ∩ S ≤ O₂(P)`. In the proof of Stellmacher (4.6), this is
applied to `K=C_{Pstar}(V)`: the product with `S` cannot be all of
`Pstar`, because both factors centralize `Z(S)` and `Pstar ≰ C`.

The proper join `KS` lies in a maximal subgroup containing `S`, which
must be the unique such subgroup `B`. Normality of `K` puts it in
`P₀=B.normalCore`. Parts (a) and (c) of (3.3) identify the image of `P₀`
modulo `O₂(P)` with the Frattini subgroup of an odd-prime residual group.
The image of `K ∩ S` is also a 2-group, hence is trivial.

Source: `refs/latex/stellmacher-n-group.tex`, (3.3), parts (a),(c), and
their use in the second paragraph of the proof of (4.6).
-/

namespace Stellmacher.SectionThree

universe u

/-- A normal subgroup that does not generate the local group with the Sylow
image has its Sylow intersection in the 2-core. -/
public theorem normal_inf_sylow_le_twoCore
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P K : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (hKP : K ≤ P)
    (hKN : (K.subgroupOf P).Normal) (hnot : ¬ P ≤ K ⊔ S) :
    K ⊓ S ≤ twoCoreAmbient P := by
  classical
  have hSP : S ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  obtain ⟨B, hBmax, hSB, hBuniq⟩ := hP.2
  have hSsubB : S.subgroupOf P ≤ B := by
    intro s hs
    obtain ⟨b, hb, heq⟩ := hSB hs
    have hbs : b = s := P.subtype_injective heq
    simpa [hbs] using hb
  have hJproper : K.subgroupOf P ⊔ S.subgroupOf P ≠ ⊤ := by
    intro hJ
    apply hnot
    have hm := congrArg (fun U : Subgroup P ↦ U.map P.subtype) hJ
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKP,
      Subgroup.map_subgroupOf_eq_of_le hSP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    exact hm.ge
  obtain ⟨B', hB'max, hJB'⟩ :=
    (eq_top_or_exists_le_coatom (K.subgroupOf P ⊔ S.subgroupOf P)).resolve_left hJproper
  have hB'eq : B' = B := hBuniq B' hB'max (by
    intro s hs
    exact ⟨⟨s, hSP hs⟩, hJB'
      ((show S.subgroupOf P ≤ K.subgroupOf P ⊔ S.subgroupOf P from le_sup_right) hs), rfl⟩)
  have hKB : K.subgroupOf P ≤ B := by
    rw [← hB'eq]
    exact le_sup_left.trans hJB'
  have hKcore : K.subgroupOf P ≤ B.normalCore := by
    let _ : (K.subgroupOf P).Normal := hKN
    exact Subgroup.normal_le_normalCore.mpr hKB
  have h33 := lemma_three_three S h P hP B B.normalCore
    ⟨hBmax, hSsubB, by
      intro B' hmax hSB'
      apply hBuniq B' hmax
      intro s hs
      exact ⟨⟨s, hSP hs⟩, hSB' hs, rfl⟩⟩
    ⟨B.normalCore_le, inferInstance, by
      intro N hN hNB
      let _ : N.Normal := hN
      exact Subgroup.normal_le_normalCore.mpr hNB⟩ hsolv
  obtain ⟨p, hp, hodd, hpgroup⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  have hpne : 2 ≠ p := by
    intro heq
    subst p
    obtain ⟨n, hn⟩ := hodd
    omega
  let R := (K ⊓ S).subgroupOf P
  let q : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
  have hRp : IsPGroup 2 R := by
    have hRp0 : IsPGroup 2 (K ⊓ S : Subgroup G) :=
      h.nontrivial_two_subgroup.2.to_le inf_le_right
    exact hRp0.of_equiv
      (Subgroup.subgroupOfEquivOfLe ((inf_le_left : K ⊓ S ≤ K).trans hKP)).symm
  have hRcore : R ≤ B.normalCore :=
    (Subgroup.subgroupOf_mono P inf_le_left).trans hKcore
  have hmap_le : R.map q ≤ twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)) := by
    calc
      R.map q ≤ B.normalCore.map q := Subgroup.map_mono hRcore
      _ = frattiniAmbient (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))) := h33.part_c
      _ ≤ _ := Subgroup.map_subtype_le _
  have hmap2 : IsPGroup 2 (R.map q) := hRp.map q
  have hmapp : IsPGroup p (R.map q) := hpgroup.to_le hmap_le
  have hmapbot : R.map q = ⊥ :=
    disjoint_self.mp (IsPGroup.disjoint_of_ne 2 p hpne _ _ hmap2 hmapp)
  intro r hr
  let rP : P := ⟨r, hKP hr.1⟩
  have hrR : rP ∈ R := hr
  have hqr : q rP ∈ R.map q := ⟨rP, hrR, rfl⟩
  rw [hmapbot] at hqr
  have hrCore : rP ∈ pCore 2 P :=
    (QuotientGroup.eq_one_iff (N := pCore 2 P) (x := rP)).mp hqr
  exact ⟨rP, hrCore, rfl⟩

end Stellmacher.SectionThree
