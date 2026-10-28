module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.Basic
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.SourceSylow.NaturalAction
public import Theory.GroupTheory.ThreeFactorPreimage

/-!
# The displayed Sylow subgroup at the end of 14.4.7

Let I = ⟨Uˣ : x ∈ L⟩ and K = O₂(I). The actual natural action has
kernel C_I(V) = K. In the frame (V₁ᵍ,V₁,V₁ˡ), the images of Uᵍ and U
are the first and second point radicals. Thus C_U(V₂) has the root-group
image with center V₁ and axis V₂. The concrete point-radical/root product
is the flag Sylow subgroup of SL₃(2).

G.2.5(3) gives K = (U∩K)(Uᵍ∩K)(Uˡ∩K). Its original factors
W₀,W₀ᵍ,W₀ˡ have this form because K is normal in I and g,l lie in I.
This W₀ = U∩K must not be confused with the source W = C_U(V₂).
The earlier normalization K ≤ N_I(U) lets us collect the full preimage
as the literal product Uᵍ C_U(V₂) C_{Uˡ}(V). Hence that product is the
join defining `candidateSylow`, and is Sylow in I. Restriction along the
actual inclusion L⊔S ≤ I supplies exactly the carrier required by the
parent complement theorem.

The genuine earlier inputs stay explicit: G.2.5(1)--(3), its kernel
identification and normalization step (using G.2.2(3)), and actual natural
coordinates from 14.3. The source choice g∈N_L(V₂)\H and l∈L\L₂T
provides the independent lines retained in `SourceNaturalFrame`.
These inputs belong to the existing Section G.2 and Section 14.3 producers;
classification assembly retains their discharge. No Sylow certificate,
candidate odd-index or candidate two-group hypothesis is used here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
G.2.5, 12.8.8(4), 14.3.10, and 14.4.7, printed pp.335--336,851,993,1009.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3Two
variable {G : Type*} [Group G]

/-- G.2.5(3) collects the kernel intersections; the marked natural action
identifies the full preimage of the flag Sylow. -/
theorem source_preimage
    (U V V₂ L : Subgroup G) (g l : G)
    (hg : g ∈ L) (hl : l ∈ L)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    (m : SourceNaturalAction (conjugateSpan U L) V hIV)
    (h₂V : V₂ ≤ V)
    (hplane : ∀ v : V, (v : G) ∈ V₂ ↔ (m.space v).toAdd 2 = 0)
    (hU : (U.subgroupOf (conjugateSpan U L)).map m.actor = SourceFlag.secondRadical)
    (hUg : ((rightConjugate U g).subgroupOf (conjugateSpan U L)).map m.actor =
      MarkedAutomorphisms.pointV)
    (hfaith : (centralizer (V : Set G)).subgroupOf (conjugateSpan U L) =
      pCore 2 (conjugateSpan U L))
    (hnorm : pCore 2 (conjugateSpan U L) ≤
      normalizer (U.subgroupOf (conjugateSpan U L) : Set (conjugateSpan U L)))
    (hcore : (pCore 2 (conjugateSpan U L) : Set (conjugateSpan U L)) =
      (U.subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U g).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U l).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _)) :
    (candidateSylow U V V₂ g l).subgroupOf (conjugateSpan U L) = borelSL.comap m.actor ∧
    (candidateSylow U V V₂ g l : Set G) =
      (rightConjugate U g : Set G) * (U ⊓ centralizer (V₂ : Set G) : Set G) *
        (rightConjugate U l ⊓ centralizer (V : Set G) : Set G) := by
  let I := conjugateSpan U L
  let A := (rightConjugate U g).subgroupOf I
  let B := (U ⊓ centralizer (V₂ : Set G)).subgroupOf I
  let C := (rightConjugate U l ⊓ centralizer (V : Set G)).subgroupOf I
  have hk : m.actor.ker = pCore 2 I := m.ker_eq.trans hfaith
  have hB : B = U.subgroupOf I ⊓ SourceFlag.planeFixer.comap m.actor := by
    ext x
    exact and_congr Iff.rfl (m.centralizer_plane V₂ h₂V hplane x)
  have hC : C = (rightConjugate U l).subgroupOf I ⊓ m.actor.ker := by
    rw [m.ker_eq]
    rfl
  have hkp : m.actor.ker ≤ SourceFlag.planeFixer.comap m.actor := ker_le_comap _ _
  have hN : m.actor.ker ≤ normalizer (B : Set I) := by
    rw [hB]
    exact (le_inf (hk ▸ hnorm) (hkp.trans (SourceFlag.planeFixer.comap m.actor).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hUb : U.subgroupOf I ⊓ m.actor.ker ≤ B ⊓ m.actor.ker := by
    rw [hB]
    exact fun x hx => ⟨⟨hx.1,hkp hx.2⟩,hx.2⟩
  have hK : (m.actor.ker : Set I) ⊆ (B ⊓ m.actor.ker : Set I) *
      (A ⊓ m.actor.ker : Set I) * (C : Set I) := by
    have he : (m.actor.ker : Set I) =
        (U.subgroupOf I ⊓ m.actor.ker : Set I) * (A ⊓ m.actor.ker : Set I) *
          ((rightConjugate U l).subgroupOf I ⊓ m.actor.ker : Set I) := by
      simpa only [hk] using hcore
    apply he.subset.trans
    apply Set.mul_subset_mul (Set.mul_subset_mul hUb le_rfl)
    exact hC.ge
  have hQ : (borelSL : Set SL) = (A.map m.actor : Set SL) * (B.map m.actor : Set SL) := by
    rw [show A.map m.actor = MarkedAutomorphisms.pointV from hUg,
      show B.map m.actor = SourceFlag.root from m.map_centralizer_plane U V₂ h₂V hplane hU]
    exact SourceFlag.borel_product
  have hCK : C ≤ m.actor.ker := hC ▸ inf_le_right
  have he := Subgroup.sup_eq_comap_threeFactor m.actor A B C borelSL hCK hN hK hQ
  have hp := Subgroup.comap_eq_threeFactor m.actor A B C borelSL hCK hN hK hQ
  have hAI : rightConjugate U g ≤ I := conjugate_le_span U L hg
  have hBI : U ⊓ centralizer (V₂ : Set G) ≤ I := inf_le_left.trans (le_conjugateSpan U L)
  have hCI : rightConjugate U l ⊓ centralizer (V : Set G) ≤ I :=
    inf_le_left.trans (conjugate_le_span U L hl)
  have hj : (candidateSylow U V V₂ g l).subgroupOf I = A ⊔ B ⊔ C := by
    rw [candidateSylow, subgroupOf_sup (sup_le hAI hBI) hCI, subgroupOf_sup hAI hBI]
  refine ⟨hj.trans he, ?_⟩
  have hh : (candidateSylow U V V₂ g l).subgroupOf I = borelSL.comap m.actor := hj.trans he
  have hs : candidateSylow U V V₂ g l ≤ I := sup_le (sup_le hAI hBI) hCI
  have hp' : ((candidateSylow U V V₂ g l).subgroupOf I : Set I) =
      (A : Set I) * (B : Set I) * (C : Set I) := by rw [hh, hp]
  have hm := congrArg (Set.image I.subtype) hp'
  simpa only [Set.image_mul, ← coe_map, coe_inf, Set.inf_eq_inter, map_subgroupOf_eq_of_le hs,
    show A.map I.subtype = rightConjugate U g from map_subgroupOf_eq_of_le hAI,
    show B.map I.subtype = U ⊓ centralizer (V₂ : Set G) from map_subgroupOf_eq_of_le hBI,
    show C.map I.subtype = rightConjugate U l ⊓ centralizer (V : Set G) from
      map_subgroupOf_eq_of_le hCI] using hm

/-- The literal Sylow carrier required by `source_complement_of_sylow`, together
with the displayed set product. The only structural premises are the actual
natural-action markings and the earlier G.2.5 kernel/generation conclusions. -/
theorem source_sylow
    (U V V₁ V₂ L : Subgroup G) (g l : G)
    (hg : g ∈ L) (hl : l ∈ L)
    (hIV : conjugateSpan U L ≤ normalizer (V : Set G))
    (m : SourceNaturalFrame U V V₁ V₂ L g l hIV)
    (hgen : conjugateSpan U L = L ⊔ U)
    (hU : (U.subgroupOf (conjugateSpan U L)).map m.actor = SourceFlag.secondRadical)
    (hUg : ((rightConjugate U g).subgroupOf (conjugateSpan U L)).map m.actor =
      MarkedAutomorphisms.pointV)
    (hfaith : (centralizer (V : Set G)).subgroupOf (conjugateSpan U L) =
      pCore 2 (conjugateSpan U L))
    (hnorm : pCore 2 (conjugateSpan U L) ≤
      normalizer (U.subgroupOf (conjugateSpan U L) : Set (conjugateSpan U L)))
    (hcore : (pCore 2 (conjugateSpan U L) : Set (conjugateSpan U L)) =
      (U.subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U g).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
      ((rightConjugate U l).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _)) :
    (candidateSylow U V V₂ g l : Set G) =
      (rightConjugate U g : Set G) * (U ⊓ centralizer (V₂ : Set G) : Set G) *
        (rightConjugate U l ⊓ centralizer (V : Set G) : Set G) ∧
    ∃ P : Sylow 2 ↥(L ⊔ candidateSylow U V V₂ g l),
      (P : Subgroup ↥(L ⊔ candidateSylow U V V₂ g l)).map
        (L ⊔ candidateSylow U V V₂ g l).subtype = candidateSylow U V V₂ g l := by
  have hp := source_preimage U V V₂ L g l hg hl hIV m.toSourceNaturalAction
    m.plane_le m.plane hU hUg hfaith hnorm hcore
  have hk : IsPGroup 2 m.actor.ker := by
    rw [m.toSourceNaturalAction.ker_eq, hfaith]
    exact pCore_isPGroup
  have hr : borelSL ≤ m.actor.range := by
    intro y hy
    rw [← SetLike.mem_coe, SourceFlag.borel_product] at hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hy
    have ha' : a ∈ ((rightConjugate U g).subgroupOf (conjugateSpan U L)).map m.actor :=
      hUg ▸ ha
    have hb' : b ∈ ((U ⊓ centralizer (V₂ : Set G)).subgroupOf (conjugateSpan U L)).map
        m.actor := (m.toSourceNaturalAction.map_centralizer_plane U V₂
          m.plane_le m.plane hU) ▸ hb
    obtain ⟨a',_,rfl⟩ := ha'
    obtain ⟨b',_,rfl⟩ := hb'
    exact ⟨a' * b', map_mul m.actor a' b'⟩
  have hmap : ((candidateSylow U V V₂ g l).subgroupOf (conjugateSpan U L)).map m.actor =
      borelSL := by
    rw [hp.1]
    exact map_comap_eq_self hr
  exact ⟨hp.2, Subgroup.exists_sylow_in_of_comap (conjugateSpan U L)
    (L ⊔ candidateSylow U V V₂ g l) (candidateSylow U V V₂ g l)
    (actor_le_span U V V₂ L hg hl hgen) le_sup_right m.actor SourceFlag.flagSylow hk hp.1 hmap⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement
