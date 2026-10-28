module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineCentralizer
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.GroupAction.PrimitiveSimplicity
public import Theory.Representation.FrattiniAction
/-!
# Excluding the affine endpoint on a split binary hexagon

With a nonbinary linear opposite endpoint, the actual Cartan-fixed
panel-kernel subgroup M has order 32. Root separation proves that the
reflection acts on M differently from every simple-root element. Since
the root actor's Borel has odd index, its action image cannot be a two-group.
The Cartan kills the root-panel kernel on M, so the action descends to the
actual root-panel image, of order 72. This is the smaller image inside
the exceptional endpoint image of order 144; no regularity is assumed.

Primitivity makes every nontrivial normal subgroup of that image have
order divisible by nine. A nonfaithful image would therefore be a two-group,
so its action on M is faithful. Burnside's Frattini kernel theorem preserves
faithfulness on M/Φ(M). The regular normal elementary nine and its freely
acting stabilizer of order eight force binary degree at least eight.
The order of M bounds that same degree by five, giving the contradiction.

All actions are restrictions or quotients of the given endpoint action.
No ambient completion is identified with its finite quotient. The original
markings and literal Chapter 12 application are in BinaryAffineExclusion.
Source: Fong--Seitz I (5E), (5I), pp.27,31--34, specialized to the odd-Cartan
binary hexagon; the degree argument is the abelian Frobenius weight bound
used in (4D). Other even Weyl orders and the full seven-row selection remain
separate obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
private theorem simple_inv (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
private theorem lengths (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) :
    Q.tits.wordLength (Q.simple j*Q.simple i) = 2 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j) = 3 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i) = 4 ∧
    Q.tits.wordLength (Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j) = 5 := by
  have h2 (b : Bool) := wordLength_alternatingWord Q b (n := 2) (by omega)
  have h3 (b : Bool) := wordLength_alternatingWord Q b (n := 3) (by omega)
  have h4 (b : Bool) := wordLength_alternatingWord Q b (n := 4) (by omega)
  have h5 (b : Bool) := wordLength_alternatingWord Q b (n := 5) (by omega)
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using And.intro (h2 true) (And.intro (h3 true) (And.intro (h4 true) (h5 true)))
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true, mul_one, mul_assoc] using And.intro (h2 false) (And.intro (h3 false) (And.intro (h4 false) (h5 false)))
  · exact (hij rfl).elim

theorem cross_root_separation (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    let C := unipotentConjugate split (Q.simple j*Q.simple i)
    simpleRoot Q split j ≤ C ∧
      rootAt Q split j (Q.simple i*Q.simple j) ≤ C ∧
      Disjoint (rootAt Q split j (Q.simple i)) C := by
  have hl := lengths Q hm i j hij
  refine ⟨(simpleRoot_le_ascent_intersection Q split _ j (by rw [hl.1,hl.2.1])).trans inf_le_right,?_,?_⟩
  · apply rootAt_le_conjugate Q split
    simp only [mul_inv_rev,simple_inv,← mul_assoc]
    rw [hl.2.2.1,hl.2.2.2]
  · have hd := congrArg (fun A => rightConjugate A
        (representative (Q.simple i) : X ⧸ Q.D))
      (disjoint_iff.mp (simpleRoot_disjoint_simpleConjugate Q split j))
    rw [rightConjugate_inf,unipotentConjugate_right split _ _ _ (representative_spec _)] at hd
    apply disjoint_iff.mpr
    exact hd.trans (by
      ext x
      exact (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).map_eq_one_iff)

/-- The reflection differs from every simple-root element on the actual fixed section. -/
theorem affine_fixed_reflection_ne_root (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144)
    (u : rankOne Q split j) (hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split j) :
    (affineFixedSection Q split j hs hp hg).numeratorAction ⟨s.val,s.mem_rankOne⟩ ≠
      (affineFixedSection Q split j hs hp hg).numeratorAction u := by
  let d := affineFixedSection Q split j hs hp hg
  let A := rootAt Q split j (Q.simple i)
  let V := LocalCover.radical Q split j
  have hAR : A ≤ simpleRemainder Q split j :=
    (show A ≤ middleRoots Q split i j from le_sup_left.trans le_sup_left).trans
      (middleRoots_le_remainder Q split hm i j hij)
  have hcard : Nat.card A = 8 := by
    have he := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at he
    change Nat.card (rootAt Q split j _) = 8
    rw [rootAt,card_rightConjugate]
    omega
  have hi : V.relIndex (simpleRemainder Q split j) = 2 := by
    rcases BinaryPanel.remainder_index_cases Q split j hp (Or.inr hg) with hr | hr
    · omega
    · exact hr.2.1
  have hAV : A ⊓ V ≠ ⊥ := by
    intro hz
    have hi' := relIndex_le_of_le_right (H := V) hAR (by rw [hi]; decide)
    rw [←inf_relIndex_left A V,hz,relIndex_bot_left,hcard,hi] at hi'
    omega
  obtain ⟨a,ha,hane⟩ := (A ⊓ V).bot_or_exists_ne_one.resolve_left hAV
  let x : d.numerator := ⟨a,ha.2,affine_cartan_centralizes_all_roots Q split j hs hp hg _ ha.1⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : d.numeratorAction r⁻¹ = d.numeratorAction u⁻¹ := by
    rw [map_inv,map_inv,he]
  have hx := congrArg (fun f : MulAut d.numerator => (f x : X ⧸ Q.D)) hei
  rw [d.numeratorAction_apply,d.numeratorAction_apply] at hx
  simp only [coe_inv,inv_inv] at hx
  change (s.val : X ⧸ Q.D)⁻¹*a*s.val = (u : X ⧸ Q.D)⁻¹*a*u at hx
  have haD : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [←rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using (show a ∈ rootAt Q split j (Q.simple i) from ha.1)
  obtain ⟨hU,hD,hd⟩ := cross_root_separation Q split hm i j hij
  have haC := (unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem
    ((unipotentConjugate split (Q.simple j*Q.simple i)).mul_mem (hU hu) (hx ▸ hD haD))
    ((unipotentConjugate split (Q.simple j*Q.simple i)).inv_mem (hU hu))
  have haC' : a ∈ unipotentConjugate split (Q.simple j*Q.simple i) := by
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using haC
  exact hane (disjoint_def.mp hd ha.1 haC')
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem rankOne_borel_index (j : Fin 2) :
    (Q.tits.B.subgroupOf (rankOne Q split j)).index = Nat.card (Panel Q j) := by
  let R := rankOne Q split j
  let : MulAction R (Panel Q j) := MulAction.compHom _ (panelAction Q j _ (rankOne_le_parabolic Q split j))
  let : MulAction.IsPretransitive R (Panel Q j) := ⟨by
    intro a b
    let := panelActor_pretransitive Q split j
    obtain ⟨r,hr⟩ := MulAction.exists_smul_eq (panelActor Q split j) a b
    exact ⟨⟨r.val.val,r.property⟩,hr⟩⟩
  have he : MulAction.stabilizer R (panelBase Q j) = Q.tits.B.subgroupOf R := by
    ext x
    change panelAction Q j _ (rankOne_le_parabolic Q split j) x (panelBase Q j) = panelBase Q j ↔ (x : X ⧸ Q.D) ∈ Q.tits.B
    rw [ReeSource.panelBase_eq_mk_one Q split j]
    change QuotientGroup.mk (⟨x,rankOne_le_parabolic Q split j x.property⟩ * 1) =
      (QuotientGroup.mk 1 : Panel Q j) ↔ _
    rw [QuotientGroup.eq]
    simp only [mul_one,inv_mem_iff]
    rfl
  rw [←he,MulAction.index_stabilizer_of_transitive]

theorem affine_fixed_panel_kernel (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    (rankOneAction Q split j).ker ≤ (affineFixedSection Q split j hs hp hg).numeratorAction.ker := by
  intro k hk
  rw [rankOneAction_ker] at hk
  have ht := RootLocalCover.rankOne_inf_kernel_le_torus Q split j ⟨k.property,hk⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [RootSection.numeratorAction_apply]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp x.property.2 _ ht)

theorem affine_fixed_action_not_two (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    ¬ IsPGroup 2 (affineFixedSection Q split j hs hp hg).numeratorAction.range := by
  let d := affineFixedSection Q split j hs hp hg
  let f := d.numeratorAction.rangeRestrict
  let R := rankOne Q split j
  let B := Q.tits.B.subgroupOf R
  let T := (Q.tits.B ⊓ Q.tits.N).subgroupOf R
  let A := (simpleRoot Q split j).subgroupOf R
  have hTK : T ≤ d.numeratorAction.ker := by
    intro t ht
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [d.numeratorAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp x.property.2 _ ht)
  have hAB : A.map f = B.map f := by
    apply le_antisymm (map_mono (subgroupOf_mono _ ((simpleRoot_le Q split j).trans split.U_le)))
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨a,ha,t,ht,he⟩ := rootActor_borel_factorization Q split j r.property hr
    let a' : R := ⟨a,(show simpleRoot Q split j ≤ R from le_sup_left) ha⟩
    let t' : R := ⟨t,ht.1⟩
    have he' : r = a'*t' := Subtype.ext he
    refine ⟨a',ha,?_⟩
    rw [he',map_mul]
    have ht' : f t' = 1 := Subtype.ext (hTK ht.2)
    rw [ht',mul_one]
  intro htwo
  have hind : (B.map f).index ∣ 9 := by
    have hh := B.index_map_dvd d.numeratorAction.rangeRestrict_surjective
    rw [rankOne_borel_index Q split j,hp] at hh
    exact hh
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hidx : (B.map f).index = 1 := Nat.eq_one_of_dvd_coprimes
    (by simpa using (by decide : Nat.Coprime 9 2).pow_right n)
    hind (hn ▸ (B.map f).index_dvd_card)
  have htop : A.map f = ⊤ := hAB.trans (index_eq_one.mp hidx)
  have hr : f ⟨s.val,s.mem_rankOne⟩ ∈ A.map f := htop ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hr
  exact affine_fixed_reflection_ne_root Q split hm i j hij s hs hp hg u hu
    (congrArg Subtype.val he).symm
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel
open MulAction
open scoped IsMulCommutative
variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
  [FaithfulSMul G Ω] [Finite Ω]

omit [Finite G] [Finite Ω] in
theorem injective_of_non_two_image {A : Type*} [Group A]
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9)
    (hg : Nat.card G = 72) (o : Ω) (f : G →* A)
    (hf : ¬ IsPGroup 2 f.range) : Function.Injective f := by
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  let : Nonempty Ω := ⟨o⟩
  apply f.ker_eq_bot_iff.mp
  by_contra hker
  have hd := card_dvd_card_normal_of_quasiprimitive (X := Ω) f.ker hker
  rw [hc] at hd
  obtain ⟨k,hk⟩ := hd
  have he := f.ker.card_mul_index
  rw [index_ker,hg,hk] at he
  have hr : Nat.card f.range ∣ 8 := ⟨k,by nlinarith⟩
  exact hf (IsPGroup.of_card_dvd_pow (p := 2) (n := 3) hr)

omit [Finite Ω] in
theorem injective_of_two_kernel {A : Type*} [Group A]
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9)
    (o : Ω) (f : G →* A) (hf : IsPGroup 2 f.ker) : Function.Injective f := by
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  let : Nonempty Ω := ⟨o⟩
  apply f.ker_eq_bot_iff.mp
  by_contra hker
  have hd := card_dvd_card_normal_of_quasiprimitive (X := Ω) f.ker hker
  rw [hc] at hd
  obtain ⟨k,hk⟩ := hf.exists_card_eq
  rw [hk] at hd
  have hh := (by decide : Nat.Prime 3).dvd_of_dvd_pow ((by decide : 3 ∣ 9).trans hd)
  norm_num at hh

theorem frobenius_nine_degree [Group.IsSolvable G]
    (ht : IsMultiplyPretransitive G Ω 2) (hc : Nat.card Ω = 9)
    (hg : Nat.card G = 72) (o : Ω)
    (hfree : ∀ g : stabilizer G o, ∀ x : Ω, x ≠ o → (g : G) • x = x → g = 1)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) :
    8 ≤ Module.finrank (ZMod 2) V := by
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  obtain ⟨N,hNn,hNe,hNc,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hNn
  let := hNe
  let : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by rw [hNc]; decide)
  have hC : Nat.card (stabilizer G o) = 8 := by
    have he := (stabilizer G o).index_mul_card
    rw [index_stabilizer_of_transitive,hc,hg] at he
    omega
  have hb := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field ρ N
    (stabilizer G o) hf (by rw [hNc]; decide) le_normalizer_of_normal (by
      intro c hc' n hn
      by_contra hne
      have hx : (n : G) • o ≠ o := by
        intro hx
        exact hne ((hreg o o).unique hx (by simp))
      apply hc'
      apply hfree c ((n : G) • o) hx
      have hcomm := mul_inv_eq_iff_eq_mul.mp hn
      rw [←mul_smul,hcomm,mul_smul,c.property])
  rwa [hC] at hb
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource MulAction
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
@[expose] def rootPanelImage (j : Fin 2) : Subgroup (Equiv.Perm (Panel Q j)) :=
  (panelAction Q j (rankOne Q split j) (rankOne_le_parabolic Q split j)).range
@[expose] def rootImageProjection (j : Fin 2) : rankOne Q split j →* rootPanelImage Q split j :=
  (panelAction Q j (rankOne Q split j) (rankOne_le_parabolic Q split j)).rangeRestrict

theorem rootPanelImage_two_pretransitive (j : Fin 2) :
    IsMultiplyPretransitive (rootPanelImage Q split j) (Panel Q j) 2 := by
  apply is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨r,hr,hr'⟩ := is_two_pretransitive_iff.mp (panelActor_two_pretransitive Q split j) hab hcd
  exact ⟨rootImageProjection Q split j ⟨r.val.val,r.property⟩,hr,hr'⟩

theorem affine_root_stabilizer (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    ((simpleRoot Q split j).subgroupOf (rankOne Q split j)).map (rootImageProjection Q split j) =
      stabilizer (rootPanelImage Q split j) (panelBase Q j) := by
  let f := rootImageProjection Q split j
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    change f u • panelBase Q j = panelBase Q j
    exact panelRoot_fixes_base Q split j ⟨u,hu⟩
  · intro x hx
    obtain ⟨r,rfl⟩ := (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective x
    have hrB : (r : X ⧸ Q.D) ∈ Q.tits.B := by
      change f r • panelBase Q j = panelBase Q j at hx
      rw [ReeSource.panelBase_eq_mk_one Q split j] at hx
      change QuotientGroup.mk (⟨r,rankOne_le_parabolic Q split j r.property⟩*1) =
        (QuotientGroup.mk 1 : Panel Q j) at hx
      have hh := QuotientGroup.eq.mp hx
      simp only [mul_one,inv_mem_iff] at hh
      exact hh
    obtain ⟨a,ha,t,ht,he⟩ := rootActor_borel_factorization Q split j r.property hrB
    let a' : rankOne Q split j := ⟨a,(show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left) ha⟩
    let t' : rankOne Q split j := ⟨t,ht.1⟩
    have htK : t' ∈ (panelAction Q j _ (rankOne_le_parabolic Q split j)).ker := by
      rw [panelAction_ker]
      exact torus_le_kernel_of_affine Q split j hs hp hg ht.2
    have he' : r = a'*t' := Subtype.ext he
    refine ⟨a',ha,?_⟩
    change f a' = f r
    rw [he',map_mul,show f t' = 1 from Subtype.ext htK,mul_one]

theorem affine_root_image_structure (j : Fin 2)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) :
    Group.IsSolvable (rootPanelImage Q split j) ∧
      Nat.card (rootPanelImage Q split j) = 72 ∧
      (∀ g : stabilizer (rootPanelImage Q split j) (panelBase Q j),
        ∀ x : Panel Q j, x ≠ panelBase Q j → (g : rootPanelImage Q split j) • x = x → g = 1) := by
  let R := rankOne Q split j
  let f := rootImageProjection Q split j
  let A := (simpleRoot Q split j).subgroupOf R
  let r : simpleRoot Q split j →* rootPanelImage Q split j :=
    f.comp (inclusion (show simpleRoot Q split j ≤ R from le_sup_left))
  have hr : Function.Injective r := by
    intro u v he
    apply simpleRoot_panelAction_injective Q split j
    exact congrArg Subtype.val he
  have hrange : r.range = A.map f := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hc : Nat.card (stabilizer (rootPanelImage Q split j) (panelBase Q j)) = 8 := by
    rw [←affine_root_stabilizer Q split j hs hp hg,←hrange,
      ←Nat.card_congr (MonoidHom.ofInjective hr).toEquiv]
    have hh := singleton_parabolic_root_index Q split j
    change Nat.card (Panel Q j) = 1 + Nat.card (simpleRoot Q split j) at hh
    omega
  let := endpoint_solvable_of_local_solvable Q split j hs
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (rankOne_le_parabolic Q split j)) (inclusion_injective _)
  have hsol : Group.IsSolvable (rootPanelImage Q split j) :=
    Group.isSolvable_of_surjective (f := f)
      (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  let : IsPreprimitive (rootPanelImage Q split j) (Panel Q j) :=
    isPreprimitive_of_is_two_pretransitive (rootPanelImage_two_pretransitive Q split j)
  have hcard := (stabilizer (rootPanelImage Q split j) (panelBase Q j)).index_mul_card
  rw [index_stabilizer_of_transitive,hp,hc] at hcard
  refine ⟨hsol,by omega,?_⟩
  intro g x hx hgfix
  have hgr : (g : rootPanelImage Q split j) ∈ r.range := by
    rw [hrange,affine_root_stabilizer Q split j hs hp hg]
    exact g.property
  obtain ⟨u,hu⟩ := hgr
  have hufix : panelRoot Q split j u • x = x := by
    change r u • x = x
    rwa [hu]
  have hue : u = 1 := (exists_unique_root_transport Q split j x x hx hx).unique
    hufix (by change (1 : panelActor Q split j) • x = x; exact one_smul _ _)
  apply Subtype.ext
  rw [←hu,hue,map_one]
  rfl
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource MulAction
open scoped MatrixGroups IsMulCommutative
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem no_affine_hexagon_of_linear
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    (hs : Group.IsSolvable (localGroup Q split j))
    (hp : Nat.card (Panel Q j) = 9) (hg : Nat.card (localGroup Q split j) = 144) : False := by
  let d := affineFixedSection Q split j hs hp hg
  let f := rootImageProjection Q split j
  have hf : Function.Surjective f :=
    (panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict_surjective
  have hk : f.ker ≤ d.numeratorAction.ker := by
    change ((panelAction Q j _ (rankOne_le_parabolic Q split j)).rangeRestrict).ker ≤ _
    rw [MonoidHom.ker_rangeRestrict,panelAction_ker]
    rw [←rankOneAction_ker]
    exact affine_fixed_panel_kernel Q split j hs hp hg
  let α : rootPanelImage Q split j →* MulAut d.numerator :=
    f.liftOfSurjective hf ⟨d.numeratorAction,hk⟩
  have ha (r : rankOne Q split j) : α (f r) = d.numeratorAction r :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have harange : α.range = d.numeratorAction.range := by
    have he : α.comp f = d.numeratorAction := MonoidHom.ext ha
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hf,←MonoidHom.range_eq_map]
  have hnon : ¬ IsPGroup 2 α.range := by
    rw [harange]
    exact affine_fixed_action_not_two Q split hm i j hij (actorReflection Q split j) hs hp hg
  obtain ⟨hsol,hcard,hfree⟩ := affine_root_image_structure Q split j hs hp hg
  let := hsol
  have hα : Function.Injective α := BinaryPanel.injective_of_non_two_image
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) α hnon
  let β := (quotientAut (frattini d.numerator)).comp α
  have hkβ : IsPGroup 2 β.ker :=
    (isPGroup_quotientAut_frattini_kernel d.isTwo).comap_of_injective α hα
  have hβ : Function.Injective β := BinaryPanel.injective_of_two_kernel
    (rootPanelImage_two_pretransitive Q split j) hp (panelBase Q j) β hkβ
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let : IsElementaryAbelian 2 (d.numerator ⧸ frattini d.numerator) :=
    isElementaryAbelian_quotient_frattini
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hρ : Function.Injective ρ := by
    intro r t he
    apply hβ
    ext x
    exact Additive.ofMul.injective (congrArg
      (fun a : Module.End (ZMod 2) (Additive (d.numerator ⧸ frattini d.numerator)) =>
        a (Additive.ofMul x)) he)
  have hdim := BinaryPanel.frobenius_nine_degree
    (rootPanelImage_two_pretransitive Q split j) hp hcard (panelBase Q j) hfree ρ hρ
  have hlow : 256 ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (d.numerator ⧸ frattini d.numerator))
    simp only [Nat.card_zmod] at he
    rw [←he] at hh
    exact hh
  have hup := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini d.numerator))
  have hc : Nat.card d.numerator = 32 :=
    affine_hexagon_fixed_section_card Q split hF hm i j hij hK μ s hs hp hg
  rw [hc] at hup
  omega
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
