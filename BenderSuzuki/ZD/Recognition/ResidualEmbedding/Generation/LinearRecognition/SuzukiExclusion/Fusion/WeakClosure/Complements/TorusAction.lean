module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.Coordinates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Foundations

/-!
# The source split-torus action on S/T

The torus normalizes T and therefore S, since S is normal in N_G(T).
Fixing a nonidentity u in U identifies the literal quotient S/T with M°
by xT ↦ [x,u]. The torus centralizes u, so these coordinates intertwine
conjugation. Its regular action on the nonidentity elements of M° then
supplies transitivity on the actual nonidentity T-cosets in S.

Source: GLS4, Chapter 2, Lemmas 14.6–14.7,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2550–2590.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The original split torus acts transitively on the literal nonidentity
T-cosets in S, with both normalization conditions discharged. -/
public theorem Context.torusQuotientAction (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hsemi : TorusSemiregular M t) : TorusQuotientAction g := by
  have hT := d.torus_normalizes_T g
  have hSN : g.S ≤ normalizer (g.T : Set G) := by
    obtain ⟨V, hV⟩ := g.S_sylow
    rw [← hV]
    exact map_subtype_le _
  have hS : residualCommutator M t ≤ normalizer (g.S : Set G) :=
    hT.trans ((normal_subgroupOf_iff_le_normalizer hSN).mp s.S_normal)
  refine ⟨hT, hS, ?_⟩
  intro a ha haT b hb hbT
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
  let := s.T_normal
  let π := QuotientGroup.mk' (g.T.subgroupOf g.S)
  let e := s.commutatorQuotientEquiv g u hu hu1
  have hne (x : g.S) (hx : (x : G) ∉ g.T) : (e (π x) : G) ≠ 1 := by
    intro he
    have he' : e (π x) = 1 := Subtype.ext he
    have hx1 : π x = 1 := e.injective (he'.trans (map_one e).symm)
    exact hx ((QuotientGroup.eq_one_iff x).mp hx1)
  obtain ⟨k, hk, _⟩ := d.torus_regular_distinguished g hsemi
    (e (π ⟨a, ha⟩)).property (hne ⟨a, ha⟩ haT)
    (e (π ⟨b, hb⟩)).property (hne ⟨b, hb⟩ hbT)
  have hka : MulAut.conj (k : G) a ∈ g.S :=
    (mem_normalizer_iff.mp (hS k.property) a).mp ha
  have hku : Commute (k : G) u :=
    mem_centralizer_iff.mp (g.U_le_centralizer hu) k
      ((show residualCommutator M t ≤ residualGenerated M z t from le_sup_right) k.property)
  have heq := s.commutatorQuotientEquiv_conj g u hu hu1 (k : G)
    (hS k.property) hku ⟨a, ha⟩
  have hq : π ⟨b, hb⟩ = π ⟨MulAut.conj (k : G) a, hka⟩ :=
    e.injective (Subtype.ext (hk.symm.trans heq.symm))
  refine ⟨k, k.property, ?_⟩
  have hm := QuotientGroup.eq_iff_div_mem.mp hq
  change b / MulAut.conj (k : G) a ∈ g.T at hm
  simpa only [div_eq_mul_inv] using hm

end BenderSuzuki.ZD.SuzukiExclusion
