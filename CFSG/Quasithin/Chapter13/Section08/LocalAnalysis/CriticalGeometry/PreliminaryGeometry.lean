module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Basic

/-!
# Preliminary geometry for 13.8.4

Vertex types force the critical geodesic to have odd length. Normality of
O₂(LT) contains the L-span. When b>3, its generators lie at mutual distance
at most four; the earlier F.7.11(3) centralization and oddness therefore make
the span abelian. At b=3, coset incidence constructs the H-conjugate of V
containing the actual endpoint line A₁. Mutual normalization and abelianness
give the two literal quadratic quotient actions and the quadratic action
of the actual star image on any genuine model of U_H/V₁.

The explicit earlier inputs are the F.9.11 lower bound, the two-core seed
containment from 13.7.3(3), equivariant F.7.11(3), the flag containments and
LT-normalization of V, F.9.13 mutual normalization, and the elementary
abelianness in the standing setup. The flag intersection and strict-span
clauses are proved in `LocalConsequences`; the permutation-module clause
is an allowed independent input to the parent source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.4,
printed p.947, using F.7.11, F.9.11 and F.9.14, printed pp.313, 321–323.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
open SectionActions
variable {G : Type*} [Group G] {L T H V : Subgroup G}

private theorem walk_even_iff {x y : Vertex L T H} (p : (graph L T H).Walk x y) :
    Even p.length ↔ x.type = y.type := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
    have hn := h.1
    cases hx : x.type <;> cases hy : y.type <;> cases hz : z.type <;> simp_all

/-- The actual endpoint conjugator preserves type, so the geodesic is odd. -/
theorem CriticalPair.length_odd (c : CriticalPair L T H V) : Odd c.path.length := by
  rw [← Nat.not_even_iff_odd, walk_even_iff]
  have ht : c.gamma.type = true := by rw [← c.gb_one]; rfl
  simp [ht]

/-- F.9.11's exclusion of lengths below three, together with the graph parity. -/
theorem CriticalPair.criticalDistance_bounds (c : CriticalPair L T H V)
    (hF911 : 2 < criticalDistance L T H V) :
    3 ≤ c.path.length ∧ Odd c.path.length := by
  exact ⟨by rw [c.length_eq]; omega, c.length_odd⟩

/-- The L-span remains in the intrinsic two-core of LT. -/
theorem UL_le_twoCore [Finite G] (V₃ : Subgroup G)
    (hU : Source.UH H V₃ ≤ (L ⊔ T).pCoreIn 2) :
    Source.UL L H V₃ ≤ (L ⊔ T).pCoreIn 2 := by
  apply conjugateSpanBy_le hU
  exact (show L ≤ L ⊔ T from le_sup_left).trans
    ((L ⊔ T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ T : Subgroup G))))

private def inLeft (l : L) : G0 L T H := ⟨l, (show L ≤ G0 L T H from le_sup_left.trans le_sup_left) l.property⟩

private theorem inLeft_zero (l : L) :
    inLeft (T := T) (H := H) l • base L T H false = base L T H false := by
  change inLeft l ∈ MulAction.stabilizer (G0 L T H) (base L T H false)
  rw [CosetGeometry.stabilizer_base]
  exact (show L ≤ L ⊔ T from le_sup_left) l.property

private def shortWalk (l : L) (h : H) :
    (graph L T H).Walk (base L T H false)
      ((inLeft l * inG0 h : G0 L T H) • base L T H false) :=
  let p : (graph L T H).Walk (base L T H false) (inG0 h • base L T H false) :=
    .cons (show (graph L T H).Adj (base L T H false) (base L T H true) from
      ⟨Bool.false_ne_true, CosetGeometry.incident_base _ _ _⟩)
      (.cons (by
        have hh := (neighbor (inG0 (L := L) (T := T) h)).symm
        rwa [inG0_one] at hh) .nil)
  (p.map (translate (inLeft l))).copy (inLeft_zero l) (mul_smul _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem shortWalk_length (l : L) (h : H) :
    (shortWalk (T := T) l h).length = 2 := by
  dsimp only [shortWalk]
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
  rfl

/-- The small-distance centralization in F.7.11(3), in its equivariant form,
forces the whole L-span to be abelian when b>3. The generators have distance
at most four; parity makes this strictly smaller than b. -/
theorem CriticalPair.UL_abelian_of_length_gt_three (c : CriticalPair L T H V)
    (V₃ : Subgroup G) (hV₃ : V₃ ≤ V) (hb : 3 < c.path.length)
    (hsmall : ∀ a b : G0 L T H,
      (graph L T H).Reachable (a • base L T H false) (b • base L T H false) →
      (graph L T H).dist (a • base L T H false) (b • base L T H false) <
        criticalDistance L T H V →
      ⁅V.map (MulAut.conj (a : G)).toMonoidHom,
        V.map (MulAut.conj (b : G)).toMonoidHom⁆ = ⊥) :
    IsMulCommutative (Source.UL L H V₃) := by
  let B : Subgroup G := ⨆ p : L × H, V.map (MulAut.conj ((p.1 : G) * p.2)).toMonoidHom
  have hUL : Source.UL L H V₃ ≤ B := by
    apply (closure_le _).mpr
    rintro _ ⟨l, hl, u, hu, rfl⟩
    have hU : Source.UH H V₃ ≤ B.comap (MulAut.conj l).toMonoidHom := by
      apply (closure_le _).mpr
      rintro _ ⟨h, hh, v, hv, rfl⟩
      apply (le_iSup (fun p : L × H => V.map
        (MulAut.conj ((p.1 : G) * p.2)).toMonoidHom) (⟨l, hl⟩, ⟨h, hh⟩))
      exact ⟨v, hV₃ hv, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact hU hu
  have hBB : B ≤ centralizer (B : Set G) := by
    apply iSup_le
    intro p
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro q
    apply commutator_eq_bot_iff_le_centralizer.mp
    let a : G0 L T H := inLeft q.1 * inG0 q.2
    let b : G0 L T H := inLeft p.1 * inG0 p.2
    let w := (shortWalk (T := T) q.1 q.2).reverse.append (shortWalk (T := T) p.1 p.2)
    have hd : (graph L T H).dist (a • base L T H false) (b • base L T H false) ≤ 4 := by
      have hw := SimpleGraph.dist_le w
      simpa only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        shortWalk_length] using hw
    obtain ⟨k, hk⟩ := c.length_odd
    have hlt : 4 < criticalDistance L T H V := by rw [← c.length_eq]; omega
    exact hsmall a b ⟨w⟩ (hd.trans_lt hlt)
  exact le_centralizer_iff_isMulCommutative.mp
    (hUL.trans (hBB.trans (centralizer_le hUL)))

/-- At length three the second vertex is the penultimate vertex. Incidence
constructs the H-conjugate of V that contains the actual line A₁. -/
theorem CriticalPair.Aone_le_conjugate_of_length_three (c : CriticalPair L T H V)
    (V₁ : Subgroup G) (hZV : V₁ ≤ V) (hNV : L ⊔ T ≤ normalizer (V : Set G))
    (hb : c.path.length = 3) :
    ∃ h : H, c.Aone V₁ ≤ V.map (MulAut.conj (h : G)).toMonoidHom := by
  have ha : (graph L T H).Adj (base L T H true) c.second := by
    have hh := c.path.adj_getVert_succ (i := 1) (by omega)
    rwa [c.first] at hh
  obtain ⟨h, hh⟩ := exists_neighbor_transporter ha
  have hg : c.gb • base L T H false = inG0 (L := L) (T := T) h • base L T H false := by
    rw [c.gb_zero, hh]
    change c.path.getVert (c.path.length - 1) = c.path.getVert 2
    rw [hb]
  have hk : ((h : G)⁻¹ * (c.gb : G)) ∈ L ⊔ T := by
    have hf : (inG0 (L := L) (T := T) h)⁻¹ * c.gb ∈ MulAction.stabilizer (G0 L T H) (base L T H false) := by
      change ((inG0 (L := L) (T := T) h)⁻¹ * c.gb) • base L T H false = base L T H false
      rw [mul_smul, hg, inv_smul_smul]
    rw [CosetGeometry.stabilizer_base] at hf
    exact hf
  have hv := mem_normalizer_iff_map_conj_eq.mp (hNV hk)
  have he := congrArg (fun W : Subgroup G => W.conjBy (h : G)) hv
  change (V.conjBy ((h : G)⁻¹ * c.gb)).conjBy (h : G) = V.conjBy (h : G) at he
  rw [← conjBy_mul, mul_inv_cancel_left] at he
  exact ⟨h, (map_mono hZV).trans he.le⟩

/-- The two literal quotient actions in 13.8.4(6) are quadratic. -/
theorem CriticalPair.quadratic_section_actions (c : CriticalPair L T H V)
    (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (hV₃ : V₃ ≤ V) (hγH : c.Vgamma ≤ H)
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (hz : H ≤ normalizer (V₁ : Set G)) :
    commutatorAction₂
      (quotientAction c.Vgamma (Source.VH H V) (Source.UH H V₃)
        (hγH.trans (le_normalizer_conjugateSpanBy V H))
        (hγH.trans (le_normalizer_conjugateSpanBy V₃ H))).range (Source.Vsection H V V₃) = ⊥ ∧
    commutatorAction₂
      (quotientAction c.Vgamma (Source.UH H V₃) V₁
        (hγH.trans (le_normalizer_conjugateSpanBy V₃ H)) (hγH.trans hz)).range
        (Source.Utilde H V₃ V₁) = ⊥ := by
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have quadratic (A Z : Subgroup G) [(Z.subgroupOf A).Normal]
      (hA : A ≤ normalizer (c.Vgamma : Set G))
      (hn : c.Vgamma ≤ normalizer (A : Set G))
      (hZ : c.Vgamma ≤ normalizer (Z : Set G)) :
      commutatorAction₂ (quotientAction c.Vgamma A Z hn hZ).range (A ⧸ Z.subgroupOf A) = ⊥ := by
    have hh := quotient_conjugation_quadratic_of_double_commutator_le
      c.Vgamma A Z c.Vgamma hn le_rfl inferInstance
      ((quadratic_of_normalizes_abelian A c.Vgamma hA inferInstance).le.trans bot_le)
      (quotientAction c.Vgamma A Z hn hZ) (quotientAction_apply c.Vgamma A Z hn hZ)
    have he : (c.Vgamma.subgroupOf c.Vgamma).map (quotientAction c.Vgamma A Z hn hZ) =
        (quotientAction c.Vgamma A Z hn hZ).range := by
      rw [subgroupOf_self, ← MonoidHom.range_eq_map]
    exact he ▸ hh
  exact ⟨quadratic (Source.VH H V) (Source.UH H V₃) (hVHend.trans (c.normalizes_Ugamma V)) _ _,
    quadratic (Source.UH H V₃) V₁ (((conjugateSpanBy_mono hV₃ le_rfl).trans hVHend).trans (c.normalizes_Ugamma V)) _ _⟩

/-- The index-two seed section is centralized by the actual terminal edge.
This discharges the edge-action premise used in 13.8.9 from the source flag
and its normalizer, rather than taking that commutator bound as a new input. -/
theorem CriticalPair.edge_commutator_le_of_flag (c : CriticalPair L T H V)
    (V₃ : Subgroup G) [IsElementaryAbelian 2 V]
    (hV₃ : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)) :
    ⁅edgeGroup L T H c.gamma c.previous,
      V.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃ := by
  let P := (L ⊔ T) ⊓ H
  have hPU : P ≤ normalizer (Source.UH H V₃ : Set G) :=
    inf_le_right.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hi := flag_intersection_of_index_two V V₃ (Source.UH H V₃)
    (le_inf hV₃ (le_conjugateSpanBy V₃ H)) hindex
    (seed_not_le_UH_of_noncentral H V V₃ hnoncentral)
  have hcard : Nat.card (V ⧸ (Source.UH H V₃).subgroupOf V) = 2 := by
    change (Source.UH H V₃).relIndex V = 2
    rw [← inf_relIndex_left V, ← hi, hindex]
  have hact : ∀ p : P, quotientAction P V (Source.UH H V₃) hnorm hPU p = 1 := by
    intro p
    obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : V ⧸ (Source.UH H V₃).subgroupOf V)).mp hcard
    ext x
    change quotientAction P V (Source.UH H V₃) hnorm hPU p x = x
    by_cases hx : x = 1
    · simp only [hx, map_one]
    · exact (huniq _ (fun he => hx ((map_eq_one_iff _
        (quotientAction P V (Source.UH H V₃) hnorm hPU p).injective).mp he))).trans
        (huniq x hx).symm
  have hbound := (quotientAction_all_eq_one_iff P V (Source.UH H V₃) hnorm hPU).mp hact
  have hedge : edgeGroup L T H c.gamma c.previous =
      P.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    have hp : vertexGroup L T H c.previous =
        (L ⊔ T).map (MulAut.conj (c.gb : G)).toMonoidHom := by
      change vertexGroup L T H (c.path.getVert (c.path.length - 1)) = _
      rw [← c.gb_zero, vertexGroup_smul, vertexGroup_base]
      rfl
    change vertexGroup L T H c.gamma ⊓ vertexGroup L T H c.previous = _
    rw [c.vertexGroup_gamma, hp, ← map_inf _ _ _ (MulAut.conj _).injective, inf_comm H]
  rw [hedge, ← map_commutator]
  exact map_mono hbound

open Representation.BinaryOffender
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open scoped commutatorElement

/-- The quadratic action of Vγ* on any genuine model of the literal UH/V₁.
Surjectivity and conjugation compatibility of the section identify linear
second differences with actual double commutators. -/
theorem CriticalPair.quadratic_star_on_Utilde {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (c : CriticalPair L T H V) (V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V) (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma) :
    IsQuadratic ρ (Source.starImage H c.Vgamma) ∧
      IsQuadratic ρ (Source.starImage H (c.Ugamma V₃)) := by
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hd : ⁅c.Vgamma, ⁅c.Vgamma, Source.UH H V₃⁆⁆ ≤ V₁ := by
    rw [commutator_comm c.Vgamma (Source.UH H V₃), commutator_comm c.Vgamma]
    exact (quadratic_of_normalizes_abelian (Source.UH H V₃) c.Vgamma
      (((conjugateSpanBy_mono hV₃ le_rfl).trans hVHend).trans (c.normalizes_Ugamma V))
      inferInstance).le.trans bot_le
  have hquad : IsQuadratic ρ (Source.starImage H c.Vgamma) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
    obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
    have hv : (s.quotient u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [← hv, s.displacement]
    apply sub_eq_zero.mp
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    exact commutator_le.mp hd a ha _ (commutator_mem_commutator hb u.property)
  refine ⟨hquad, ?_⟩
  have hle : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
    map_mono (subgroupOf_mono H (map_mono (conjugateSpanBy_mono hV₃ le_rfl)))
  exact fun a ha b hb v => hquad a (hle ha) b (hle hb) v

/-- The actual star image is quadratic on VH/UH, for its genuine factored
conjugation action. This explicitly identifies the actor as Vγ* in H/O₂(H). -/
theorem CriticalPair.quadratic_star_on_Vsection (c : CriticalPair L T H V)
    (V₃ : Subgroup G) [IsElementaryAbelian 2 (Source.VH H V)]
    (hγH : c.Vgamma ≤ H)
    (hVHend : Source.VH H V ≤ vertexGroup L T H c.gamma)
    (action : Source.Hstar H →* MulAut (Source.Vsection H V V₃))
    (hact : ∀ h : H, ∀ u : Source.VH H V,
      action (QuotientGroup.mk' (pCore 2 H) h)
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)) u) =
      QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V))
        ⟨(h : G) * (u : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H h.property) u).mp u.property⟩) :
    commutatorAction₂ ((Source.starImage H c.Vgamma).map action) (Source.Vsection H V V₃) = ⊥ := by
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hd : ⁅⁅Source.VH H V, c.Vgamma⁆, c.Vgamma⁆ ≤ Source.UH H V₃ :=
    (quadratic_of_normalizes_abelian (Source.VH H V) c.Vgamma
      (hVHend.trans (c.normalizes_Ugamma V)) inferInstance).le.trans bot_le
  have hh := quotient_conjugation_quadratic_of_double_commutator_le
    H (Source.VH H V) (Source.UH H V₃) c.Vgamma (le_normalizer_conjugateSpanBy V H)
    hγH inferInstance hd (action.comp (QuotientGroup.mk' (pCore 2 H))) hact
  have he : (Source.starImage H c.Vgamma).map action =
      (c.Vgamma.subgroupOf H).map (action.comp (QuotientGroup.mk' (pCore 2 H))) :=
    map_map _ _ _
  exact (congrArg (fun D : Subgroup (MulAut (Source.Vsection H V V₃)) =>
    commutatorAction₂ D (Source.Vsection H V V₃)) he).trans hh

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
