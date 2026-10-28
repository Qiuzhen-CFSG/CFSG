module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstTwentyFiveModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveSectionTernarySieve

/-!
# The PSL₂(25) outer witness in the original flag geometry

Pass to the ambient two-core quotient and restrict the full quotient Sylow
to the containing C-component. The existing local-section transport keeps
the A₅ quotient literal. The PSL₂(25) calculation supplies an outer Sylow
actor there. Surjectivity sends inner automorphisms of the original
two-core quotient to inner automorphisms of its image, so this witness
lifts to the original Sylow intersection.

The chosen-flag application works inside N_G(V₁). It derives the A₅
marking, proper inclusion, and local membership from the preceding
rank-one quotient, then returns an element of T intersect K acting
outwardly on the original L₁/O₂(L₁). When the preceding pointwise L₁
action is supplied, that same element centralizes the entire V₁,
including C_V(L).

These are the outer-witness assertions used in the source's PSL₂(25)
exclusion. The natural-module contradiction, the other remaining sieve
rows and final 11.1.1--11.1.3 assembly remain with
qt-d-1222-natural-relative-components. The preceding quotient and
pointwise flag facts are supplied by qt-d-1222-natural-flag-cartan,
with their ultimate discharge in qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed p.762, using A.3.12(8), A.3.14 and the literal
solvable-kernel local-section transport.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.TwentyFive

private theorem inner_action_transport {A B : Type*} [Group A] [Group B]
    (q : A →* B) (hq : Function.Surjective q)
    (a : MulAut A) (b : MulAut B) (he : ∀ x, q (a x) = b (q x))
    (hi : (quotientAut (pCore 2 A)) a ∈ MulAut.innerSubgroup (A ⧸ pCore 2 A)) :
    (quotientAut (pCore 2 B)) b ∈ MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  have hc : pCore 2 A ≤ (pCore 2 B).comap q := by
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map q hq,pCore_isPGroup.map q⟩
  let d := QuotientGroup.map (pCore 2 A) (pCore 2 B) q hc
  obtain ⟨z,hz⟩ := hi
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
  refine ⟨QuotientGroup.mk' (pCore 2 B) (q z),?_⟩
  ext y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) y
  obtain ⟨x,rfl⟩ := hq y
  have hh := congrArg d (DFunLike.congr_fun hz (QuotientGroup.mk' (pCore 2 A) x))
  simp only [quotientAut_apply_mk,MulAut.conj_apply,map_mul,map_inv,
    d,QuotientGroup.map_mk',he] at hh
  rw [quotientAut_apply_mk,MulAut.conj_apply]
  simpa only [QuotientGroup.mk'_apply] using hh

open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- Lift the model witness to the original Sylow intersection with the
containing C-component. The ambient two-core quotient preserves the local
A₅ section, and innerness descends along the literal image map. -/
theorem containing_has_outer_sylow
    (P : Sylow 2 G) (B K : Subgroup G) (hK : K.IsCComponent)
    (hB : B ∈ ChapterA.Section03.localCComponents P)
    (hBK : B < K) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    ∃ t : G, ∃ ht : t ∈ (P : Subgroup G), t ∈ K ∧
      (quotientAut (pCore 2 B)) (B.normalizerMonoidHom ⟨t,hPB ht⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := K.map q
  let A := B.map q
  have hAC : A ≤ C := map_mono hBK.le
  let E := A.subgroupOf C
  let eC : C ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm
  have hmC : ClassicalGroup.IsPSL C 2 25 := hm.of_mulEquiv eC
  obtain ⟨S,hS,hl,hn,hne,⟨eE⟩⟩ :=
    proper_five_section_in_containing_image P B K hK hB hBK hPB eB
  obtain ⟨s,hs,hout⟩ := local_five_has_outer_sylow S E hl hn hne eE hmC
  obtain ⟨t,htK,hts⟩ := s.property
  change q t = s.val at hts
  have htP : t ∈ (P : Subgroup G) := by
    have hh : q t ∈ (P : Subgroup G).map q := by
      rw [hts]
      change s ∈ ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) :
        Subgroup (G ⧸ pCore 2 G)).subgroupOf C
      rwa [← hS]
    change t ∈ ((P : Subgroup G).map q).comap q at hh
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
      (pCore_isPGroup.le_sylow_of_normal P)] at hh
    exact hh
  refine ⟨t,htP,htK,?_⟩
  intro hi
  apply hout
  let d : E ≃* A := subgroupOfEquivOfLe hAC
  let r : B →* E := d.symm.toMonoidHom.comp (q.subgroupMap B)
  have hr : Function.Surjective r := d.symm.surjective.comp (q.subgroupMap_surjective B)
  apply inner_action_transport r hr _ _ _ hi
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change q (t * x.val * t⁻¹) = s.val * q x.val * s.val⁻¹
  simp only [map_mul,map_inv,hts]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.TwentyFive

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The PSL₂(25) branch supplies an element of T intersect K inducing an
outer automorphism on the actual first residual quotient. The A₅ marking,
properness and relative local-family membership are derived here. -/
theorem first_twentyFive_outer_on_rankOne
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G), t ∈ K ∧
      Closure.coreQuotientAction (f.Li 0) ⟨t,f.sylow_normalizes_Li 0 ht⟩ ∉
        MulAut.innerSubgroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := by
  have heB : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card F = 4 by simpa [hfour] using hF)
    exact ⟨e.trans a⟩
  obtain ⟨eB⟩ := heB
  have hlt : f.Li 0 < K := lt_of_le_of_ne hLK (by
    intro he
    have hb : Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) = 60 := by
      rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
      norm_num
    have hc : Nat.card (K ⧸ pCore 2 K) = 7800 := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
      exact (Nat.card_congr e.toEquiv).trans (Theory.PSL2.TwentyFive.card hF)
    rw [he] at hb
    omega)
  let H := normalizer (f.Vi 0 : Set G)
  have hTH : (T : Subgroup G) ≤ H := f.invariant 0
  have hCH : K ≤ H := hK.1
  have hBH : f.Li 0 ≤ H := hLK.trans hCH
  let P := T.subtype hTH
  let B := (f.Li 0).subgroupOf H
  let C := K.subgroupOf H
  let b : B ≃* f.Li 0 := subgroupOfEquivOfLe hBH
  let k : C ≃* K := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  have hlocal : B ∈ ChapterA.Section03.localCComponents P := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hTH hBH).mp
      ⟨hBH,flag_mem_local_of_model D S f 0 hm⟩
    exact hh.1
  have hBC : B < C := by
    refine lt_of_le_of_ne (comap_mono hLK) ?_
    intro he
    apply hlt.ne
    simpa only [B,C,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hCH] using
      congrArg (map H.subtype) he
  have hPB : (P : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht x
    exact f.sylow_normalizes_Li 0 ht x
  obtain ⟨t,ht,htC,hout⟩ := TwentyFive.containing_has_outer_sylow P B C hK.2
    hlocal hBC hPB (bq.trans eB) (hk.of_mulEquiv kq)
  refine ⟨t.val,ht,htC,?_⟩
  intro hi
  apply hout
  apply TwentyFive.inner_action_transport b.symm.toMonoidHom b.symm.surjective _ _ _ hi
  intro x
  rfl

/-- In the actual first-normalizer geometry the outer witness fixes the
entire original V₁, including its retained central attachment. -/
theorem first_twentyFive_outer_centralizes_point
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G), t ∈ K ∧
      t ∈ centralizer (f.Vi 0 : Set G) ∧
      Closure.coreQuotientAction (f.Li 0) ⟨t,f.sylow_normalizes_Li 0 ht⟩ ∉
        MulAut.innerSubgroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := by
  obtain ⟨t,ht,htK,hout⟩ := first_twentyFive_outer_on_rankOne D S f hm hfour hK hLK hk
  exact ⟨t,ht,htK,
    subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl hm hfix hK hLK htK,hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
