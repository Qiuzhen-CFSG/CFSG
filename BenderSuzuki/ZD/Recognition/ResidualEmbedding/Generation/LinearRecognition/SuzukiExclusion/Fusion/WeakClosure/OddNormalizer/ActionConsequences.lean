module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Burnside

/-!
# Fixed subgroups and fusion for the actual odd-normalizer action

The action formula identifies every torus fixed subgroup with the literal
image of U. Disjointness from M° preserves the order of U in this quotient.
Preservation under N_M(S)/S is then transported to the full normalizer in
M/M°, where the existing Burnside theorem supplies quotient weak closure.

The action remains an explicit intermediate input; this module does not
construct it or prove its Fitting alternatives.
Source: GLS4, Chapter 2, Lemma 14.9, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
open Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

@[expose] public def involutionImage (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    Subgroup (pointQuotient d) := (g.U.subgroupOf M).map (pointProjection d)

public theorem involutionImage_le (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    involutionImage d g ≤ sylowImage d g := map_mono (subgroupOf_mono M g.U_le_S)

public theorem involutionImage_card (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    Nat.card (involutionImage d g) = Nat.card g.U := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let U := g.U.subgroupOf M
  have hker : (pi.subgroupMap U).ker = ⊥ := by
    apply bot_unique
    intro u hu
    have hq : pi (u : M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    have hA : (u : M) ∈ A.subgroupOf M := (QuotientGroup.eq_one_iff (u : M)).mp hq
    exact Subtype.ext (Subtype.ext (g.closure_disjoint_U.le_bot ⟨hA, u.property⟩))
  let e := MulEquiv.ofBijective (pi.subgroupMap U)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, pi.subgroupMap_surjective U⟩
  exact (Nat.card_congr e.toEquiv).symm.trans
    (Nat.card_congr (subgroupOfEquivOfLe (g.U_le_S.trans g.S_le_M)).toEquiv)

public theorem ActionData.torus_fixed_iff (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (a : ActionData d g) (hsemi : TorusSemiregular M t)
    {x : quotient g} (hx : x ∈ torusImage g) (hx1 : x ≠ 1) (v : sylowImage d g) :
    a.action x v = v ↔ (v : pointQuotient d) ∈ involutionImage d g := by
  obtain ⟨n, hn, rfl⟩ := hx
  have hn1 : ((n : M) : G) ≠ 1 := by
    intro he
    have hn1 : n = 1 := Subtype.ext (Subtype.ext he)
    exact hx1 (by rw [hn1, map_one])
  have hcent := d.quotient_sylow_torus_centralizer g hsemi hn hn1
  change sylowImage d g ⊓ centralizer ({pointProjection d (n : M)} : Set (pointQuotient d)) =
    involutionImage d g at hcent
  constructor
  · intro hv
    rw [← hcent]
    refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : pointProjection d (n : M) * (v : pointQuotient d) *
        (pointProjection d (n : M))⁻¹ = v :=
      (a.conjugation n v).symm.trans (congrArg Subtype.val hv)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hv
    rw [← hcent] at hv
    apply Subtype.ext
    rw [a.conjugation]
    rw [← mem_centralizer_singleton_iff.mp hv.2, mul_inv_cancel_right]

/-- Preservation under the literal N_M(S)/S action implies full quotient
normalizer invariance, since every normalizer element lifts to N_M(S). -/
public theorem ActionData.normalizerInvariant (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (a : ActionData d g)
    (hinv : ∀ x : quotient g, ∀ v : sylowImage d g,
      (v : pointQuotient d) ∈ involutionImage d g →
      (a.action x v : pointQuotient d) ∈ involutionImage d g) :
    QuotientNormalizerInvariant d g := by
  change normalizer (sylowImage d g : Set (pointQuotient d)) ≤
    normalizer (involutionImage d g : Set (pointQuotient d))
  apply le_normalizer_iff.mpr
  intro x hx u hu
  have hn := d.quotient_sylow_normalizer g
  change (normalizerInM g).map (pointProjection d) =
    normalizer (sylowImage d g : Set (pointQuotient d)) at hn
  rw [← hn] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  let nN : normalizerInM g := ⟨n, hn⟩
  let v : sylowImage d g := ⟨u, involutionImage_le d g hu⟩
  have h := hinv (projection g nN) v hu
  rwa [a.conjugation] at h

/-- The actual Burnside consumer, with no abstract quotient replacement. -/
public theorem ActionData.quotientFusion (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (he : ElementaryQuotient d g)
    (a : ActionData d g)
    (hinv : ∀ x : quotient g, ∀ v : sylowImage d g,
      (v : pointQuotient d) ∈ involutionImage d g →
      (a.action x v : pointQuotient d) ∈ involutionImage d g) :
    QuotientFusion d g :=
  quotientFusion_of_elementary_normalizer d g s he (a.normalizerInvariant d g hinv)

end BenderSuzuki.ZD.SuzukiExclusion.OddNormalizer
