module
public import Stellmacher.SectionTen.TenOneSmallCenterNormalizer
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreFrattini
public import Stellmacher.SectionNine.VertexNormalizedTwoSubgroupSolvable
public import Theory.GroupTheory.MixedCoreOvergroup

/-!
# The small Wstar normalizer after the mixed-closure bound

In the actual small Section Ten context, let N be the ambient normalizer
of the mapped middle-core centralizer Wstar. Suppose the terminal-center
closure under the lower mixed core of N joined with the terminal edge lies
in the mapped middle center. Then N equals the mapped middle stabilizer.
The closure containment is explicit; its quadratic-action proof is separate.

Take the middle-stabilizer conjugate closure D of this mixed closure. It
lies in the middle plane and is nontrivial because it contains the terminal
center line. Pulling back through the supplied embedding, the absence of
an invariant middle line forces D to be the whole plane. The normal mixed
layer of N normalizes each generator of D, so the proved center-normalizer
identity puts that layer in the middle stabilizer. The mixed-core overgroup
theorem now identifies its core with the core of N. Finally, the exact
Frattini identity makes the middle plane N-invariant, and the same
center-normalizer identity gives the required equality.

All closures, core maps and Frattini maps use their actual ambient carriers.
The mixed closure is not assumed normal in N. This supplies the abbreviated
normality transfer in Stellmacher (10.1)(a3)(9), Journal of Algebra 190
(1997), printed pp.61–62, using the already proved assertion (7).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The mixed-closure bound determines the ambient normalizer of the literal Wstar. -/
public theorem ten_one_small_centralizer_normalizer_of_mixed_closure_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    let N := Subgroup.normalizer (Wstar.map embedding : Set H)
    let L := ((pPrimeCore 2 (N ⧸ pCore 2 N)).comap
      (QuotientGroup.mk' (pCore 2 N))).map N.subtype
    let U := L ⊔ (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a').map embedding
    Stellmacher.conjugateClosure ((ZAt ctx.Γ ctx.criticalPath.a').map embedding) U ≤
      (ZAt ctx.Γ middle).map embedding → N = (GAt ctx.Γ middle).map embedding := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ GeneratedNeighborhoodV Γ middle
  let Wstar := QAt Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  let N := normalizer (Wstar.map embedding : Set H)
  let Rn := pCore 2 N
  let Ln := (pPrimeCore 2 (N ⧸ Rn)).comap (QuotientGroup.mk' Rn)
  let L := Ln.map N.subtype
  let U := L ⊔ (GAt Γ middle ⊓ GAt Γ cp.a').map embedding
  let P := GAt Γ middle
  let M := P.map embedding
  let Zg := ZAt Γ middle
  let Z := Zg.map embedding
  let Qg := QAt Γ middle
  let Q := Qg.map embedding
  let Bseed := (ZAt Γ cp.a').map embedding
  let W1 := Stellmacher.conjugateClosure Bseed U
  let D := Stellmacher.conjugateClosure W1 M
  change W1 ≤ Z → N = M
  intro hWZ
  have hpacket := ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  change P ≤ normalizer (Wstar : Set G) ∧ _ at hpacket
  let _ : IsElementaryAbelian 2 Wstar := hpacket.2.1
  have hWne : Wstar ≠ ⊥ := by
    intro hh
    have hc := hpacket.2.2.1
    change Nat.card Wstar = 8 ∨ Nat.card Wstar = 16 at hc
    rw [hh, card_bot] at hc
    omega
  let _ : Group.IsSolvable N := ambient_vertex_normalized_two_subgroup_solvable
    ctx.toAmbientSectionNineContext middle Wstar hWne
      (IsElementaryAbelian.isPGroup 2 Wstar) hpacket.1
  have hMN : M ≤ N := (map_mono hpacket.1).trans (Wstar.le_normalizer_map embedding)
  have hNZ : normalizer (Z : Set H) = M :=
    ten_one_small_center_normalizer ctx middle hpath hsmall hmodel
  have hNL : N ≤ normalizer (L : Set H) := by
    have hh := Ln.le_normalizer_map N.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
  have hseed (C J : Subgroup H) : C ≤ Stellmacher.conjugateClosure C J := by
    intro c hc
    exact Subgroup.subset_closure ⟨1, ⟨c, hc⟩, by simp⟩
  have hactors (C J : Subgroup H) :
      J ≤ normalizer (Stellmacher.conjugateClosure C J : Set H) := by
    rw [Stellmacher.conjugateClosure, le_normalizer_closure_iff]
    intro a ha x hx
    obtain ⟨b, c, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨a * (b : H), J.mul_mem ha b.property⟩, c, ?_⟩
    simp only [mul_inv_rev]
    group
  have hLW : L ≤ normalizer (W1 : Set H) := le_sup_left.trans (hactors Bseed U)
  have hMD : M ≤ normalizer (D : Set H) := hactors W1 M
  have hDZ : D ≤ Z := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨m, w, rfl⟩
    exact (mem_normalizer_iff.mp (hNZ.ge m.property) w).mp (hWZ w.property)
  have hLD : L ≤ normalizer (D : Set H) := by
    rw [show D = Stellmacher.conjugateClosure W1 M from rfl,
      Stellmacher.conjugateClosure, le_normalizer_closure_iff]
    intro a ha x hx
    obtain ⟨m, w, rfl⟩ := hx
    have hconj : (m : H)⁻¹ * a * m ∈ L := by
      have hh := (mem_normalizer_iff.mp (hNL (N.inv_mem (hMN m.property))) a).mp ha
      simpa only [inv_inv] using hh
    have hpoint : ((m : H)⁻¹ * a * m) * w * ((m : H)⁻¹ * a * m)⁻¹ ∈ W1 :=
      (mem_normalizer_iff.mp (hLW hconj) w).mp w.property
    apply Subgroup.subset_closure
    refine ⟨m, ⟨_, hpoint⟩, ?_⟩
    group
  let Dg := D.comap embedding
  have hDmap : Dg.map embedding = D :=
    map_comap_eq_self (hDZ.trans (map_le_range _ _))
  have hDgZ : Dg ≤ Zg := by
    have hh := comap_mono (f := embedding) hDZ
    change Dg ≤ (Zg.map embedding).comap embedding at hh
    rwa [comap_map_eq_self_of_injective ctx.embedding_injective] at hh
  have hPDg : P ≤ normalizer (Dg : Set G) := by
    apply le_trans ?_ (D.le_normalizer_comap embedding)
    intro p hp
    exact hMD (mem_map_of_mem embedding hp)
  have hBcard : Nat.card Bseed = 2 := by
    rw [show Bseed = (ZAt Γ cp.a').map embedding from rfl,
      card_map_of_injective ctx.embedding_injective]
    obtain ⟨actor, _, halign⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    exact (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
      (by rw [ctx.critical_length]; decide) cp.a' ⟨actor, halign⟩).1
  have hBD : Bseed ≤ D := (hseed Bseed U).trans (hseed W1 M)
  have hDgne : Dg ≠ ⊥ := by
    intro hh
    have hD : D = ⊥ := by rw [← hDmap, hh, Subgroup.map_bot]
    have hc := card_le_of_le hBD
    rw [hBcard, hD, card_bot] at hc
    omega
  have hDgcardNeTwo := ten_one_no_invariant_middle_line ctx middle hpath Dg hDgZ hPDg
  have hZgcard : Nat.card Zg = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hpositive := (one_lt_card_iff_ne_bot Dg).mpr hDgne
  have hdiv := card_dvd_of_le hDgZ
  rw [hZgcard] at hdiv
  have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have hDgcard : Nat.card Dg = 4 := by
    interval_cases h : Nat.card Dg <;> norm_num at *
  have hDg : Dg = Zg := eq_of_le_of_card_ge hDgZ (by rw [hDgcard, hZgcard])
  have hD : D = Z := by rw [← hDmap, hDg]
  have hLM : L ≤ M := by rw [← hNZ, ← hD]; exact hLD
  let Mn := M.subgroupOf N
  have hLnMn : Ln ≤ Mn := by
    intro l hl
    exact hLM (mem_map_of_mem N.subtype hl)
  have hcore := mapped_pCore_eq_of_prime_mixed_core_le 2 Mn hLnMn
  let eM : P ≃* Mn := (P.equivMapOfInjective embedding ctx.embedding_injective).trans
    (subgroupOfEquivOfLe hMN).symm
  have hNcore : Rn.map N.subtype = Q := by
    calc
      Rn.map N.subtype = ((pCore 2 Mn).map Mn.subtype).map N.subtype := by rw [hcore]
      _ = ((pCore 2 P).map eM.toMonoidHom).map (N.subtype.comp Mn.subtype) := by
        rw [pCore_map_iso 2 eM, map_map]
      _ = ((pCore 2 P).map P.subtype).map embedding := by rw [map_map, map_map]; rfl
      _ = Q := congrArg (Subgroup.map embedding) (Γ.twoCoreAt_def middle).symm
  have hNQ : N ≤ normalizer (Q : Set H) := by
    have hh := Rn.le_normalizer_map N.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hNcore] at hh
  have hZQ : Zg ≤ Qg := by
    rw [show Zg = omegaOneCenter Qg from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact map_subtype_le _
  let eQ : Qg ≃* Q := Qg.equivMapOfInjective embedding ctx.embedding_injective
  have hPhi : (frattini Qg).map eQ.toMonoidHom = frattini Q := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective eQ.surjective)
    · intro q hq
      refine ⟨eQ.symm q, ?_, eQ.apply_symm_apply q⟩
      exact frattini_le_comap_frattini_of_surjective
        (φ := eQ.symm.toMonoidHom) eQ.symm.surjective hq
  have hPhiMap : (frattini Q).map Q.subtype = Z := by
    rw [← hPhi, map_map]
    have hcomp : Q.subtype.comp eQ.toMonoidHom = embedding.comp Qg.subtype := by ext q; rfl
    rw [hcomp, ← map_map,
      ten_one_small_middle_core_frattini ctx middle hpath hsmall hmodel,
      map_subgroupOf_eq_of_le hZQ]
  have hNZ' : N ≤ normalizer (Z : Set H) := by
    rw [← hPhiMap]
    exact hNQ.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q (frattini Q))
  exact le_antisymm (hNZ'.trans_eq hNZ) hMN

end Stellmacher.SectionTen
