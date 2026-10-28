module
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# A residual commutator supplement without Sylow normality

For a solvable member `P` of Stellmacher's P-set, any subgroup `V` of the
specified Sylow subgroup `S` that is not contained in `O₂(P)` satisfies
`[O²(P),V] ⊔ S = P`. Normality of `V` inside `S` is not required.

Take the normal closure `T` of `V` inside `S`; (3.4) gives `[O²(P),T]=O²(P)`.
Inside `P`, put `K=[O²(P),V] ⊔ S`. The residual normalizes its commutator
with `V`, and `P=O²(P)S`, so every conjugate of that commutator belongs to
`K`. Consequently it lies in the normal core of `K`. The normal-closure
commutator bound extends this containment to `T`, forcing the residual into
`K`. Residual–Sylow generation now gives the asserted equality.

This supplies the unqualified relative generation step in the proof of
Stellmacher (9.1)(8), Journal of Algebra 190 (1997), p.47, using (3.4) on
p.22; see `refs/files/stellmacher-n-group.pdf`. The source's subgroup need
not already be normal in a Sylow subgroup.
-/

namespace Stellmacher.SectionThree
open Subgroup
open scoped Pointwise

private theorem commutator_le_core_of_supplement
    {G : Type*} [Group G] (R S V : Subgroup G) [R.Normal]
    (hgen : R ⊔ S = ⊤) : ⁅R,V⁆ ≤ (⁅R,V⁆ ⊔ S).normalCore := by
  intro x hx g
  have hg : g ∈ S ⊔ R := by rw [sup_comm, hgen]; trivial
  obtain ⟨s, hs, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hg
  have hxconj : r * x * r⁻¹ ∈ ⁅R,V⁆ :=
    (mem_normalizer_iff.mp (normalizer_commutator_ge_left R V hr) x).mp hx
  have hh := (⁅R,V⁆ ⊔ S).mul_mem
    ((⁅R,V⁆ ⊔ S).mul_mem (mem_sup_right hs) (mem_sup_left hxconj))
    ((⁅R,V⁆ ⊔ S).inv_mem (mem_sup_right hs))
  change (s*r)*x*(s*r)⁻¹ ∈ ⁅R,V⁆ ⊔ S
  simpa only [mul_inv_rev, mul_assoc] using hh

/-- A subgroup of the Sylow outside the two-core has a residual commutator
that supplements that Sylow subgroup. -/
public theorem residual_commutator_sup_sylow_of_not_le_core
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (V : Subgroup G)
    (hVS : V ≤ S) (hnot : ¬ V ≤ twoCoreAmbient P) :
    ⁅twoResidualAmbient P,V⁆ ⊔ S = P := by
  classical
  obtain ⟨sylow, hsylow⟩ := hP.1.2.1
  have hSP : S ≤ P := by rw [← hsylow]; exact map_subtype_le _
  have hVP : V ≤ P := hVS.trans hSP
  let L := normalClosure (V.subgroupOf S : Set S)
  let T := L.map S.subtype
  have hTS : T ≤ S := map_subtype_le _
  have hVT : V ≤ T := by
    rw [← map_subgroupOf_eq_of_le hVS]
    exact map_mono le_normalClosure
  have hTn : (T.subgroupOf S).Normal := by
    have ht : T.subgroupOf S = L := comap_map_eq_self_of_injective S.subtype_injective L
    rw [ht]
    exact normalClosure_normal
  have hRT : ⁅twoResidualAmbient P,T⁆ = twoResidualAmbient P :=
    (lemma_three_four S h P hP T ⟨hTS,hTn⟩ hsolv).resolve_left
      (fun hh => hnot (hVT.trans hh))
  let R := twoResidualSubgroup P
  let SP := S.subgroupOf P
  let VP := V.subgroupOf P
  let TP := T.subgroupOf P
  let C := normalClosure (VP : Set P)
  have hRn : R.Normal := by
    unfold R twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact normal_iInf_normal (fun N => normal_iInf_normal (fun hN => hN.1))
  let := hRn
  have hgen : R ⊔ SP = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hSP,
      ← MonoidHom.range_eq_map, range_subtype]
    exact twoResidual_sup_sylowImage ⟨sylow,hsylow⟩
  have hTPC : TP ≤ C := by
    have hLN : L ≤ (C.comap (inclusion hSP)) := by
      apply normalClosure_le_normal
      intro v hv
      apply le_normalClosure
      exact hv
    intro t ht
    obtain ⟨v, hv, hvt⟩ := ht
    have hh := hLN hv
    change (inclusion hSP v) ∈ C at hh
    have heq : inclusion hSP v = t := Subtype.ext hvt
    rwa [heq] at hh
  have hnative : ⁅R,TP⁆ = R := by
    apply map_injective P.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (hTS.trans hSP)]
    exact hRT
  have hRle : R ≤ ⁅R,VP⁆ ⊔ SP := by
    calc
      R = ⁅R,TP⁆ := hnative.symm
      _ ≤ (⁅R,VP⁆ ⊔ SP).normalCore := (commutator_mono le_rfl hTPC).trans
        (commutator_normalClosure_le_of_normal R VP (⁅R,VP⁆ ⊔ SP).normalCore
          (commutator_le_core_of_supplement R SP VP hgen))
      _ ≤ ⁅R,VP⁆ ⊔ SP := normalCore_le _
  have htop : ⁅R,VP⁆ ⊔ SP = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le hRle le_sup_right
  have hm := congrArg (map P.subtype) htop
  rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hVP,
    map_subgroupOf_eq_of_le hSP, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

end Stellmacher.SectionThree
