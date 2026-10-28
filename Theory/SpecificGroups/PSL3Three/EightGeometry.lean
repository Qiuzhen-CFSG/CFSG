module
public import Theory.SpecificGroups.PSL3Three.FourNormalizer.FullNormalizer
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.NormalizerActionSurjective
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
/-!
# Elementary eights in Aut(PSL₃(3))

Every elementary eight intersects the inner automorphism group in a four;
it equals that four's full pointwise fixer. Simultaneous diagonalization of
fours therefore proves conjugacy of all elementary eights, even by inner
automorphisms. In diagonal coordinates the fixer is the product of the inner
four with inverse transpose. The latter fixes exactly the four-normalizer S₄.
The full normalizer action on the inner four is S₃, so its kernel, this exact
elementary eight, is its embedded two-core.

Source: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559, outer case.
The model statements retain the full automorphism group and actual inner map.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Three.EightGeometry
open FourGeometry GraphWitnesses.EightCentralizers GraphWitnesses.EightCentralizers.GraphModel
local notation "τ" => graph (ZMod 3)
@[expose] noncomputable def diagonal : Subgroup PSL := diagonalFour.map equiv.toMonoidHom
@[expose] def fullFixer (E : Subgroup PSL) : Subgroup (MulAut PSL) :=
  fixingSubgroup (MulAut PSL) (E : Set PSL)
@[expose] def innerFour (E : Subgroup PSL) : Subgroup (MulAut PSL) := E.map MulAut.conj

theorem centralizer_innerFour (E : Subgroup PSL) :
    centralizer (innerFour E : Set (MulAut PSL)) = fullFixer E := by
  ext a
  change a ∈ centralizer (innerFour E : Set (MulAut PSL)) ↔
    a ∈ fixingSubgroup (MulAut PSL) (E : Set PSL)
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro ha x hx
    change a x = x
    apply MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
    have hc := ha (MulAut.conj x) (mem_map.mpr ⟨x, hx, rfl⟩)
    have he : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by ext y; simp
    rw [he, ← hc, mul_inv_cancel_right]
  · intro ha
    change ∀ y ∈ E, a y = y at ha
    rintro _ ⟨x, hx, rfl⟩
    apply MulEquiv.ext
    intro y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, ha x hx]

theorem diagonal_elementary : IsElementaryAbelian 2 diagonal := by
  let : IsElementaryAbelian 2 diagonalFour :=
    { toIsMulCommutative := le_centralizer_iff_isMulCommutative.mp
        (le_of_eq centralizer_diagonalFour.symm)
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        rintro ⟨x, i, rfl⟩
        apply Subtype.ext
        have h : ∀ i : Fin 4, diagonalElement i ^ 2 = 1 := by decide
        exact h i }
  exact IsElementaryAbelian.map equiv.toMonoidHom

theorem diagonal_card : Nat.card diagonal = 4 := by
  rw [diagonal, card_map_of_injective equiv.injective, card_diagonalFour]

theorem graph_fixes_diagonal (x : PSL) (hx : x ∈ diagonal) : τ x = x := by
  obtain ⟨s, ⟨i, rfl⟩, rfl⟩ := hx
  have h : ∀ i : Fin 4, graphSL (ZMod 3) (diagonalElement i) = diagonalElement i := by decide
  change τ (equiv (diagonalElement i)) = equiv (diagonalElement i)
  rw [equiv_apply]
  change project (graphSL (ZMod 3) (diagonalElement i)) = project (diagonalElement i)
  rw [h]

theorem diagonal_normalizer : normalizer (diagonal : Set PSL) = (τ).fixedSubgroup := by
  rw [diagonal, ← map_equiv_normalizer_eq, normalizer_diagonalFour, graph_fixed_eq_monomial]
  change monomialSL.map equiv.toMonoidHom = monomialSL.map project
  congr 1
  ext x
  exact equiv_apply x

theorem diagonal_fixer_eq : fullFixer diagonal = innerFour diagonal ⊔ zpowers τ := by
  let : IsElementaryAbelian 2 diagonal := diagonal_elementary
  have hcent : centralizer (diagonal : Set PSL) = diagonal :=
    centralizer_four diagonal diagonal_elementary diagonal_card
  have hτ : τ ∈ fullFixer diagonal := (mem_fixingSubgroup_iff _).mpr graph_fixes_diagonal
  have hinner : innerFour diagonal ≤ fullFixer diagonal := by
    rw [← centralizer_innerFour]
    let : IsElementaryAbelian 2 (innerFour diagonal) := IsElementaryAbelian.map MulAut.conj
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply le_antisymm ?_ (sup_le hinner (zpowers_le.mpr hτ))
  intro a ha
  obtain ⟨g, hg | hg⟩ := automorphism_inner_or_inner_graph a
  · have hc : g ∈ diagonal := by
      rw [← hcent]
      intro x hx
      have h := (mem_fixingSubgroup_iff _).mp ha x hx
      change a x = x at h
      rw [hg, MulAut.conj_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hg]
    exact mem_sup_left (mem_map.mpr ⟨g, hc, rfl⟩)
  · have hc : g ∈ diagonal := by
      rw [← hcent]
      intro x hx
      have h := (mem_fixingSubgroup_iff _).mp ha x hx
      change a x = x at h
      rw [hg, MulAut.mul_apply, graph_fixes_diagonal x hx, MulAut.conj_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hg]
    exact (innerFour diagonal ⊔ zpowers τ).mul_mem
      (mem_sup_left (mem_map.mpr ⟨g, hc, rfl⟩)) (mem_sup_right (mem_zpowers τ))

theorem diagonal_fixer_elementary : IsElementaryAbelian 2 (fullFixer diagonal) := by
  rw [diagonal_fixer_eq]
  let : IsElementaryAbelian 2 diagonal := diagonal_elementary
  let : IsElementaryAbelian 2 (innerFour diagonal) := IsElementaryAbelian.map MulAut.conj
  let : IsElementaryAbelian 2 (zpowers τ) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (graph_sq (ZMod 3))
  apply IsElementaryAbelian.sup_of_le_centralizer
  rw [centralizer_innerFour]
  exact zpowers_le.mpr ((mem_fixingSubgroup_iff _).mpr graph_fixes_diagonal)

theorem four_conj_diagonal (E : Subgroup PSL) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) : ∃ g : PSL, E.map (MulAut.conj g).toMonoidHom = diagonal := by
  let : IsElementaryAbelian 2 E := hE
  let A := E.map equiv.symm.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map equiv.symm.toMonoidHom
  obtain ⟨g, hg⟩ := exists_conj_diagonalFour A
    (by rw [card_map_of_injective equiv.symm.injective, hc])
  refine ⟨equiv g, ?_⟩
  have hf : (MulAut.conj (equiv g)).toMonoidHom = equiv.toMonoidHom.comp
      ((MulAut.conj g).toMonoidHom.comp equiv.symm.toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    change equiv g * x * (equiv g)⁻¹ = equiv (g * equiv.symm x * g⁻¹)
    rw [map_mul, map_mul, map_inv, equiv.apply_symm_apply]
  rw [hf, ← Subgroup.map_map, ← Subgroup.map_map, hg]
  rfl

theorem four_fixer_elementary (E : Subgroup PSL) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) : IsElementaryAbelian 2 (fullFixer E) := by
  obtain ⟨g, hg⟩ := four_conj_diagonal E hE hc
  let d := MulAut.fixingSubgroupEquivOfMap (MulAut.conj g) E diagonal hg
  let : IsElementaryAbelian 2 (fixingSubgroup (MulAut PSL) (diagonal : Set PSL)) := diagonal_fixer_elementary
  exact IsElementaryAbelian.of_injective d.toMonoidHom d.injective

private theorem map_innerFour (E : Subgroup PSL) (a : MulAut PSL) :
    (innerFour E).map (MulAut.congr a).toMonoidHom = innerFour (E.map a.toMonoidHom) := by
  rw [innerFour, innerFour, Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact MulAut.congr_conj a x

private theorem map_fixed (a f : MulAut PSL) :
    f.fixedSubgroup.map a.toMonoidHom = (MulAut.congr a f).fixedSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change a (f (a.symm (a y))) = a y
    rw [a.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp hy]
  · intro hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply a.injective
    exact ((MulAut.mem_fixedSubgroup _ _).mp hx).trans (a.apply_symm_apply x).symm

/-- Each four has a graph-type outer involution whose entire fixed group
is the four-normalizer and whose join with the inner four is its full fixer. -/
theorem four_graph_marking (E : Subgroup PSL) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) : ∃ f : MulAut PSL,
    orderOf f = 2 ∧ f ∉ MulAut.innerSubgroup PSL ∧
    f.fixedSubgroup = normalizer (E : Set PSL) ∧
    fullFixer E = innerFour E ⊔ zpowers f := by
  obtain ⟨g, hg⟩ := four_conj_diagonal E hE hc
  let a := MulAut.conj g
  let b := MulAut.congr a
  let f := b.symm τ
  have hbf : b f = τ := b.apply_symm_apply τ
  refine ⟨f, (b.symm.orderOf_eq τ).trans graph_orderOf, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    apply graph_not_inner
    refine ⟨a x, ?_⟩
    rw [← MulAut.congr_conj, hx]
    exact hbf
  · apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [map_fixed, hbf, map_equiv_normalizer_eq, hg, diagonal_normalizer]
  · apply Subgroup.map_injective (f := b.toMonoidHom) b.injective
    change (fixingSubgroup (MulAut PSL) (E : Set PSL)).map (MulAut.congr a).toMonoidHom = _
    rw [MulAut.map_fixingSubgroup_congr, hg, Subgroup.map_sup, map_innerFour,
      hg, MonoidHom.map_zpowers]
    change fullFixer diagonal = innerFour diagonal ⊔ zpowers (b f)
    rw [hbf, diagonal_fixer_eq]

/-- The full normalizer of the inner four has exactly the elementary-eight
pointwise fixer as its embedded two-core. -/
theorem four_normalizer_twoCore (E : Subgroup PSL) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) :
    (pCore 2 (normalizer (innerFour E : Set (MulAut PSL)))).map
      (normalizer (innerFour E : Set (MulAut PSL))).subtype = fullFixer E := by
  let : IsElementaryAbelian 2 E := hE
  let U := innerFour E
  let N := normalizer (U : Set (MulAut PSL))
  let F := fullFixer E
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map MulAut.conj
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    change _ < Nat.card (innerFour E)
    rw [innerFour, card_map_of_injective
      (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot), hc]
    decide)
  let : IsKleinFour U := ⟨by
    change Nat.card (innerFour E) = 4
    rw [innerFour, card_map_of_injective
      (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot), hc],
    IsElementaryAbelian.exponent_eq_prime⟩
  have hFN : F ≤ N := by
    change fullFixer E ≤ normalizer (innerFour E : Set (MulAut PSL))
    rw [← centralizer_innerFour]
    exact centralizer_le_normalizer _
  have hker : U.normalizerMonoidHom.ker = F.subgroupOf N := by
    rw [normalizerMonoidHom_ker, centralizer_innerFour]
  have hcardker : Nat.card U.normalizerMonoidHom.ker = 8 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hFN).toEquiv]
    exact card_four_fixer E hE hc
  have hcardN : Nat.card N = 48 := card_four_fullNormalizer E hE hc
  have hi : (centralizer (U : Set (MulAut PSL))).relIndex N = 6 := by
    have hh := U.normalizerMonoidHom.ker.card_mul_index
    rw [hcardker, hcardN, U.normalizerMonoidHom_ker] at hh
    change 8 * (centralizer (U : Set (MulAut PSL))).relIndex N = 48 at hh
    omega
  have hsurj : Function.Surjective U.normalizerMonoidHom :=
    U.normalizerMonoidHom_surjective_of_index_eq_card (by rw [IsKleinFour.card_mulAut]; exact hi)
  have hle : pCore 2 N ≤ F.subgroupOf N := by
    rw [← hker]
    exact IsKleinFour.twoCore_le_ker_of_surjective U U.normalizerMonoidHom hsurj
  have hFl : F.subgroupOf N ≤ pCore 2 N := by
    let : IsElementaryAbelian 2 F := four_fixer_elementary E hE hc
    let : IsElementaryAbelian 2 (F.subgroupOf N) := IsElementaryAbelian.subgroupOf hFN
    have hn : (F.subgroupOf N).Normal := hker ▸ inferInstance
    exact le_sSup ⟨hn, IsElementaryAbelian.isPGroup 2 _⟩
  rw [le_antisymm hle hFl, map_subgroupOf_eq_of_le hFN]

theorem inner_index_two : (MulAut.innerSubgroup PSL).index = 2 := by
  have hc : Nat.card (MulAut.innerSubgroup PSL) = 5616 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot)).toEquiv]
    exact card_PSL
  have h := (MulAut.innerSubgroup PSL).card_mul_index
  rw [hc, FourGeometry.card_fullAutomorphismGroup] at h
  omega

/-- Every elementary eight is exactly the full fixer of its actual inner four. -/
theorem eight_eq_four_fixer (B : Subgroup (MulAut PSL))
    (hB : IsElementaryAbelian 2 B) (hc : Nat.card B = 8) :
    let E := B.comap (MulAut.conj : PSL →* MulAut PSL)
    IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ B = fullFixer E := by
  let : IsElementaryAbelian 2 B := hB
  let E := B.comap (MulAut.conj : PSL →* MulAut PSL)
  let I := MulAut.innerSubgroup PSL
  let D := I.subgroupOf B
  have hinj := MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective MulAut.conj hinj B
  obtain ⟨b, hb, hbi⟩ := elementary_eight_has_outer B hB hc
  have hi : D.index = 2 := I.subgroupOf_index_eq_two B inner_index_two (fun h => hbi (h hb))
  have hd : Nat.card D = 4 := by
    have hh := D.card_mul_index
    rw [hi, hc] at hh
    omega
  let f : E →* D :=
    { toFun := fun x => ⟨⟨MulAut.conj x.val, x.property⟩, ⟨x.val, rfl⟩⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one MulAut.conj
      map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul MulAut.conj x.val y.val }
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (hinj (congrArg (fun d : D => ((d : B) : MulAut PSL)) h))
  have hfs : Function.Surjective f := by
    rintro ⟨⟨a, ha⟩, g, hg⟩
    exact ⟨⟨g, show MulAut.conj g ∈ B from hg.symm ▸ ha⟩, Subtype.ext (Subtype.ext hg)⟩
  have hec : Nat.card E = 4 :=
    (Nat.card_congr (MulEquiv.ofBijective f ⟨hfi, hfs⟩).toEquiv).trans hd
  refine ⟨inferInstance, hec, eq_of_le_of_card_ge ?_ ?_⟩
  · rw [← centralizer_innerFour]
    intro a ha
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hB.toIsMulCommutative)
      (⟨MulAut.conj x, hx⟩ : B) ⟨a, ha⟩)
  · rw [hc]
    exact (card_four_fixer E inferInstance hec).le

/-- Even inner automorphisms are transitive on elementary-eight subgroups
of the full automorphism group. -/
theorem eight_conj_standard (B : Subgroup (MulAut PSL))
    (hB : IsElementaryAbelian 2 B) (hc : Nat.card B = 8) :
    ∃ g : PSL, B.map (MulAut.conj (MulAut.conj g)).toMonoidHom = fullFixer diagonal := by
  obtain ⟨hE, hEc, hBfix⟩ := eight_eq_four_fixer B hB hc
  obtain ⟨g, hg⟩ := four_conj_diagonal _ hE hEc
  refine ⟨g, ?_⟩
  rw [hBfix]
  change (fixingSubgroup (MulAut PSL) (_ : Set PSL)).map
    (MulAut.congr (MulAut.conj g)).toMonoidHom = fullFixer diagonal
  rw [MulAut.map_fixingSubgroup_congr, hg]
  rfl

/-- The full automorphism group is transitive on its elementary eights. -/
theorem eight_conjugate (B C : Subgroup (MulAut PSL))
    (hB : IsElementaryAbelian 2 B) (hBc : Nat.card B = 8)
    (hC : IsElementaryAbelian 2 C) (hCc : Nat.card C = 8) :
    ∃ a : MulAut PSL, B.map (MulAut.conj a).toMonoidHom = C := by
  obtain ⟨g, hg⟩ := eight_conj_standard B hB hBc
  obtain ⟨h, hh⟩ := eight_conj_standard C hC hCc
  refine ⟨(MulAut.conj h)⁻¹ * MulAut.conj g, ?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj (MulAut.conj h)).toMonoidHom)
    (MulAut.conj (MulAut.conj h)).injective
  rw [hh, Subgroup.map_map]
  have he : (MulAut.conj (MulAut.conj h)).toMonoidHom.comp
      (MulAut.conj ((MulAut.conj h)⁻¹ * MulAut.conj g)).toMonoidHom =
      (MulAut.conj (MulAut.conj g)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply]
    group
  rw [he, hg]

/-- Centralizers of an actor inside the actual inner group retain its fixed subgroup. -/
theorem inner_inf_actor_centralizer (f : MulAut PSL) :
    MulAut.innerSubgroup PSL ⊓ centralizer ({f} : Set (MulAut PSL)) =
      f.fixedSubgroup.map (MulAut.conj : PSL →* MulAut PSL) := by
  ext a
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨g, ?_, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
    have he : MulAut.conj (f g) = f * MulAut.conj g * f⁻¹ := by ext x; simp
    rw [he, ← mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    apply MulEquiv.ext
    intro x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      (MulAut.mem_fixedSubgroup _ _).mp hg]

/-- Normalizers inside the actual inner group retain the original normalizer. -/
theorem inner_inf_four_normalizer (E : Subgroup PSL) :
    MulAut.innerSubgroup PSL ⊓ normalizer (innerFour E : Set (MulAut PSL)) =
      (normalizer (E : Set PSL)).map (MulAut.conj : PSL →* MulAut PSL) := by
  have hm (g : PSL) :
      (innerFour E).map (MulAut.conj (MulAut.conj g)).toMonoidHom =
      innerFour (E.map (MulAut.conj g).toMonoidHom) := map_innerFour E (MulAut.conj g)
  have hn (g : PSL) : MulAut.conj g ∈ normalizer (innerFour E : Set (MulAut PSL)) ↔
      g ∈ normalizer (E : Set PSL) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (innerFour E).map (MulAut.conj (MulAut.conj g)).toMonoidHom = innerFour E ↔ _
    rw [hm, mem_normalizer_iff_map_conj_eq]
    exact (Subgroup.map_injective (f := (MulAut.conj : PSL →* MulAut PSL))
      (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot)).eq_iff
  ext a
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, (hn g).mp hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (hn g).mpr hg⟩

/-- The intrinsic graph marking, written entirely inside Aut(PSL₃(3)). -/
theorem four_graph_inner_marking (E : Subgroup PSL) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = 4) : ∃ f : MulAut PSL,
    orderOf f = 2 ∧ f ∉ MulAut.innerSubgroup PSL ∧
    MulAut.innerSubgroup PSL ⊓ centralizer ({f} : Set (MulAut PSL)) =
      MulAut.innerSubgroup PSL ⊓ normalizer (innerFour E : Set (MulAut PSL)) ∧
    Nonempty ((MulAut.innerSubgroup PSL ⊓ normalizer (innerFour E : Set (MulAut PSL)) :
      Subgroup (MulAut PSL)) ≃* Equiv.Perm (Fin 4)) ∧
    fullFixer E = innerFour E ⊔ zpowers f := by
  obtain ⟨f, hf, hout, hfixed, hgen⟩ := four_graph_marking E hE hc
  refine ⟨f, hf, hout, ?_, ?_, hgen⟩
  · rw [inner_inf_actor_centralizer, inner_inf_four_normalizer, hfixed]
  · obtain ⟨e⟩ := normalizer_four_nonempty_equiv E hE hc
    exact ⟨(MulEquiv.subgroupCongr (inner_inf_four_normalizer E)).trans
      (((normalizer (E : Set PSL)).equivMapOfInjective MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot)).symm.trans e)⟩

end Matrix.PSL3Three.EightGeometry
