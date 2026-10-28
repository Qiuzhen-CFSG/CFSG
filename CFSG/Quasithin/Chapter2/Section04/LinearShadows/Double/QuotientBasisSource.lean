module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.TorusSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.StabilizerSource
public import Theory.GroupTheory.SylowCommutingJoin
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupTheory.CyclicPairRank


/-!
# The original residual quotient in the paired linear case

The commuting blocks and the original Sylow factorization give an
index-two block stabilizer in H. Their prescribed Sylow subgroups show
J(S)=S∩L₀. Thus a two-rank bound on H/L₀ descends to S/J(S), and the
original index-two overgroup has quotient two-rank at most three.
Every transport uses the literal original subgroups and quotient maps.

Source: Aschbacher--Smith, proof of 2.4.7, printed p.540.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open LinearDouble LinearShadows.Double ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- Every element of the original parabolic preserves the two block set. -/
theorem DoubleLinearSourceSetup.parabolic_permutes
    (c : DoubleLinearSourceSetup d M₀ n) (h : d.H) :
    (d.block.map d.H.subtype).conjBy (h:G) = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy (h:G) = c.second := by
  let L := d.block.map d.H.subtype
  have hn₁ : d.L0.map d.H.subtype ≤ normalizer (L : Set G) := by
    rw [←c.join]
    exact sup_le L.le_normalizer (c.commutes.trans (Subgroup.centralizer_le_normalizer _))
  have hn₂ : d.L0.map d.H.subtype ≤ normalizer (c.second : Set G) := by
    rw [←c.join]
    exact sup_le ((le_centralizer_iff.mp c.commutes).trans (Subgroup.centralizer_le_normalizer _))
      c.second.le_normalizer
  obtain ⟨l,s,he⟩ := d.factorization h
  have heG : (h:G) = ((l:d.H):G) * ((s:d.H):G) := congrArg Subtype.val he
  rw [heG,←conjBy_conjBy]
  rcases c.permutes (s:d.H) (mem_map_of_mem d.H.subtype s.property) with hfix | hswap
  · rw [hfix]
    exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (hn₁ (mem_map_of_mem d.H.subtype l.property)))
  · rw [hswap]
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hn₂ (mem_map_of_mem d.H.subtype l.property)))

omit [Finite G] in
/-- The intrinsic factor stabilizer has the same two-element orbit. -/
theorem DoubleLinearSourceSetup.parabolic_stabilizer_index
    (c : DoubleLinearSourceSetup d M₀ n) :
    (normalizer (d.block : Set d.H)).index = 2 := by
  have hsecond : c.second ≤ d.H := (le_sup_right.trans_eq c.join).trans (map_subtype_le _)
  have hp : ∀ h : d.H, d.block.conjBy h = d.block ∨
      d.block.conjBy h = c.second.subgroupOf d.H := by
    intro h
    rcases c.parabolic_permutes h with ha | hb
    · exact Or.inl (map_injective d.H.subtype_injective (by rw [map_conjBy_hom]; exact ha))
    · exact Or.inr (map_injective d.H.subtype_injective (by
        rw [map_conjBy_hom,map_subgroupOf_eq_of_le hsecond]
        exact hb))
  obtain ⟨s,hs,he⟩ := c.exchange
  let sh : d.H := ⟨s,(map_subtype_le (d.S:Subgroup d.H)) hs⟩
  have hm : d.block.conjBy sh ≠ d.block := by
    intro hh
    have hh' := congrArg (map d.H.subtype) hh
    rw [map_conjBy_hom] at hh'
    exact c.second_ne (he.symm.trans hh')
  simpa only [relIndex_top_right] using
    normalizer_relIndex_eq_two_of_pair (⊤ : Subgroup d.H) d.block
      (c.second.subgroupOf d.H) (fun h _ => hp h) sh (mem_top _) hm

omit [Finite G] in
/-- The original residual is contained in the factor stabilizer. -/
theorem DoubleLinearSourceSetup.residual_le_parabolic_stabilizer
    (c : DoubleLinearSourceSetup d M₀ n) :
    d.L0 ≤ normalizer (d.block : Set d.H) := by
  have hn : d.L0.map d.H.subtype ≤ normalizer (d.block.map d.H.subtype : Set G) := by
    rw [←c.join]
    exact sup_le (d.block.map d.H.subtype).le_normalizer
      (c.commutes.trans (Subgroup.centralizer_le_normalizer _))
  intro l hl
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply map_injective d.H.subtype_injective
  change (d.block.conjBy l).map d.H.subtype = d.block.map d.H.subtype
  rw [map_conjBy_hom]
  exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_map_of_mem d.H.subtype hl))

omit [Finite G] in
/-- An element outside the intrinsic stabilizer exchanges the actual blocks. -/
theorem DoubleLinearSourceSetup.parabolic_outside_exchanges
    (c : DoubleLinearSourceSetup d M₀ n) (x : d.H)
    (hx : x ∉ normalizer (d.block : Set d.H)) :
    (d.block.map d.H.subtype).conjBy (x:G) = c.second := by
  apply (c.parabolic_permutes x).resolve_left
  intro hh
  apply hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply map_injective d.H.subtype_injective
  change (d.block.conjBy x).map d.H.subtype = d.block.map d.H.subtype
  rw [map_conjBy_hom]
  exact hh
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open LinearDouble LinearShadows.Double ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

private theorem pgroup_inf_join_le_of_sylow_factors
    (A B R S : Subgroup G) (hcomm : A ≤ centralizer (B : Set G))
    (hRS : R ≤ S) (hS : IsPGroup 2 S)
    (P : Sylow 2 A) (Q : Sylow 2 B)
    (hP : (P : Subgroup A).map A.subtype ≤ R)
    (hQ : (Q : Subgroup B).map B.subtype ≤ R) : S ⊓ (A ⊔ B) ≤ R := by
  let C : Bool → Subgroup G := fun b => if b then A else B
  let Ps : ∀ b, Sylow 2 (C b) := fun b => by cases b; exact Q; exact P
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (hcomm hy x hx)
    · exact (hcomm hx y hy).symm
    · exact (hij rfl).elim
  have hPR : ∀ i, (Ps i : Subgroup (C i)).map (C i).subtype ≤ R := by
    intro i
    cases i
    · exact hQ
    · exact hP
  obtain ⟨W,hW⟩ := exists_sylow_iSup_le_of_commuting C hc Ps R hPR
  have hgen : (⨆ i, C i) = A ⊔ B := by simp [C,iSup_bool_eq]
  have hWS : (W : Subgroup (⨆ i, C i : Subgroup G)) ≤ S.subgroupOf (⨆ i, C i) := by
    intro w hw
    exact hRS (hW (mem_map_of_mem _ hw))
  have he := W.is_maximal' hS.comap_subtype hWS
  intro g hg
  have hg' : g ∈ ⨆ i, C i := hgen.symm ▸ hg.2
  have hw : (⟨g,hg'⟩ : (⨆ i, C i : Subgroup G)) ∈ (W : Subgroup _) := he ▸ hg.1
  exact hW (mem_map_of_mem _ hw)

/-- The original Thompson subgroup is the literal residual Sylow intersection. -/
theorem LinearDouble.SourceTorusData.residual_sylow_intersection
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c) :
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) =
      ((d.S : Subgroup d.H).map d.H.subtype) ⊓ d.L0.map d.H.subtype := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hRL : R ≤ d.L0.map d.H.subtype := by
    change Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤ _
    rw [td.geometry.span,←c.join]
    exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
  apply le_antisymm (le_inf hRS hRL)
  rw [←c.join]
  exact pgroup_inf_join_le_of_sylow_factors _ _ R S (le_centralizer_iff.mp c.commutes)
    hRS (d.S.isPGroup'.map d.H.subtype) td.borel.first.sylow td.borel.second.sylow
    (td.borel.first.sylow_eq.le.trans inf_le_left)
    (td.borel.second.sylow_eq.le.trans inf_le_left)
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open LinearDouble
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}
omit [Finite G] in
/-- The same exchange identity on the exact intrinsic blocks. -/
theorem DoubleLinearSourceSetup.parabolic_outside_exchanges_intrinsic
    (c : DoubleLinearSourceSetup d M₀ n) (x : d.H)
    (hx : x ∉ normalizer (d.block : Set d.H)) :
    d.block.conjBy x = c.second.subgroupOf d.H := by
  apply map_injective d.H.subtype_injective
  rw [map_conjBy_hom,map_subgroupOf_eq_of_le
    ((le_sup_right.trans_eq c.join).trans (map_subtype_le _))]
  exact c.parabolic_outside_exchanges x hx
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open LinearDouble LinearShadows.Double ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

/-- Restricting the residual quotient to the original Sylow has exactly J(S) as kernel. -/
theorem LinearDouble.SourceTorusData.sylow_quotient_rank
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c)
    (hquot : let : d.L0.Normal := d.L0_normal; primeRank 2 (d.H ⧸ d.L0) ≤ 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
      (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
    primeRank 2 (S ⧸ R.subgroupOf S) ≤ 2 := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let : d.L0.Normal := d.L0_normal
  let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let f : S →* d.H ⧸ d.L0 := (QuotientGroup.mk' d.L0).comp (inclusion (map_subtype_le _))
  have hk : f.ker = R.subgroupOf S := by
    ext s
    change QuotientGroup.mk' d.L0 (inclusion (map_subtype_le _) s) = 1 ↔ (s:G)∈R
    constructor
    · intro hs
      have hs := (QuotientGroup.eq_one_iff (N := d.L0) (inclusion (map_subtype_le _) s)).mp hs
      change (s:G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      rw [td.residual_sylow_intersection]
      exact ⟨s.property,mem_map_of_mem d.H.subtype hs⟩
    · intro hs
      have hh := td.residual_sylow_intersection.le hs
      apply (QuotientGroup.eq_one_iff (N := d.L0) (inclusion (map_subtype_le _) s)).mpr
      exact (mem_map_iff_mem d.H.subtype_injective).mp hh.2
  let fq : S ⧸ R.subgroupOf S →* d.H ⧸ d.L0 :=
    QuotientGroup.lift (R.subgroupOf S) f hk.ge
  have hfi : Function.Injective fq := by
    apply fq.ker_eq_bot_iff.mp
    rw [show fq = QuotientGroup.lift (R.subgroupOf S) f hk.ge from rfl,
      QuotientGroup.ker_lift,hk,QuotientGroup.map_mk'_self]
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 fq hfi).trans hquot

/-- The index-two original overgroup adds at most one to quotient rank. -/
theorem LinearDouble.SourceTorusData.overgroup_quotient_rank
    {c : DoubleLinearSourceSetup d M₀ n} (td : SourceTorusData c)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (hquot : let : d.L0.Normal := d.L0_normal; primeRank 2 (d.H ⧸ d.L0) ≤ 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let : (R.subgroupOf M₀).Normal := normal_subgroupOf_of_le_normalizer
      (c.original.R_normal.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
    primeRank 2 (M₀ ⧸ R.subgroupOf M₀) ≤ 3 := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let : (R.subgroupOf M₀).Normal := normal_subgroupOf_of_le_normalizer
    (c.original.R_normal.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  let B := S.subgroupOf M₀
  let N := R.subgroupOf M₀
  let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let e : B ≃* S := subgroupOfEquivOfLe c.original.R_le_M
  have he : (N.subgroupOf B).map e.toMonoidHom = R.subgroupOf S := by
    ext r
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact hb
    · intro hr
      exact ⟨⟨⟨r,c.original.R_le_M r.property⟩,r.property⟩,hr,rfl⟩
  let eq : (B ⧸ N.subgroupOf B) ≃* (S ⧸ R.subgroupOf S) :=
    QuotientGroup.congr _ _ e he
  have hBrank : primeRank 2 (B ⧸ N.subgroupOf B) ≤ 2 := by
    rw [primeRank_equiv 2 eq]
    exact td.sylow_quotient_rank hquot
  exact primeRank_quotient_le_add_of_index_le N B
    (subgroupOf_mono M₀ hRS) (show B.index ≤ 2^1 by change S.relIndex M₀ ≤ 2^1; change S.relIndex M₀ = 2 at hi; omega) hBrank
end CFSG.Quasithin.Chapter2
