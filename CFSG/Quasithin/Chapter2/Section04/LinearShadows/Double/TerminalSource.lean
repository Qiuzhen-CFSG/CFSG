module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.CoreCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognitionRank
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.RankSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.MixedNormalizerSource
/-!
# Closing the double linear branch after Thompson stability

When the original Sylow subgroup has index two in the ambient Sylow group,
the original torus, new local group and core-centralization producers give
a genuine component. Its refined catalogue supplies an odd prime of rank
two; the independent torus gives rank three in a two-local subgroup,
contradicting quasithinness. All component and model premises are discharged
on the literal source carriers. The four-family normalizer theorem reduces
the remaining case exactly to the earlier Thompson stability identity.

Source: Aschbacher–Smith 2.4.7, printed pp.540–541.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open LinearDouble
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {n : ℕ}

/-- The actual index-two Sylow case closes by the independent torus and
rank-two component, with all generated-group premises proved from source. -/
theorem DoubleLinearSourceSetup.false_of_index_two_sylow
    (T : Sylow 2 G) (c : DoubleLinearSourceSetup d (T : Subgroup G) n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2) : False := by
  obtain ⟨a⟩ := c.torus_data hG T hM hTM hu hST hL hST.le le_rfl hi
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R₁ := elementaryAbelianMaxJ S ⊓ d.block.map d.H.subtype
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  let S₁ := (T : Subgroup G) ⊓ normalizer (R₁ : Set G)
  let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  obtain ⟨hBS,hiB,hx,_,hKS,hKN,hRcore⟩ := c.adjusted_pair_geometry T hST.le hST.le le_rfl hi a
  obtain ⟨hXmax,hpair,hSylow,hlocal⟩ := c.adjusted_pair_local_source T hG hM hTM hu hST.le hi a
  have hLX : c.second≤X := le_sup_left.trans le_sup_left
  have hBX : B≤X := hBS.trans le_sup_right
  have hlocal' : c.second∈Chapter1.L G B :=
    ((Chapter1.mem_LIn_iff_subgroupOf hBX hLX).mpr hlocal).2
  let : Group.IsPerfect c.second := Chapter1.mem_L_isPerfect hlocal'
  have hc := c.adjusted_pair_core_centralizes T hST.le hST.le le_rfl hi a hSylow
  have hcore : twoCore X≠⊥ := fun he => a.geometry.nontrivial_first (bot_unique (he ▸ hRcore))
  obtain ⟨p,hp,ho,hd,hrank⟩ := LinearShadows.Double.source_pair_odd_rank d c hG T hM hTM hu
    a.x B S₁ hx hBS hiB hcore hc hSylow hlocal hKN hKS (Or.inr hXmax) hpair
  have hRp : IsPGroup 2 R₁ := (d.S.isPGroup'.map d.H.subtype).to_le
    (inf_le_left.trans (sSup_le (fun _ h => h.1)))
  apply false_of_conjugate_generated_rank R₁ a.borel.first.torus c.second a.x
    hG.quasithin hRp a.geometry.nontrivial_first a.borel.first.normalizes_sylow
    a.geometry.faithful_first a.geometry.cross_first a.geometry.fixes_first_sylow
    a.geometry.fixes_first_torus hp ho _ hrank
  rwa [a.borel.first.card]

/-- The earlier four-family normalizer theorem turns Thompson stability
into the literal index-two Sylow case above. -/
theorem DoubleLinearSourceSetup.false_of_thompson_stable
    {M₀ : Subgroup G} (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hJ : elementaryAbelianMaxJ M₀ = elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) : False := by
  have he := c.sylow_eq_of_thompson_stable hG T hM hTM hu hST.le hMT hi hJ
  subst M₀
  exact c.false_of_index_two_sylow T hG hM hTM hu hST hL hi

end CFSG.Quasithin.Chapter2
