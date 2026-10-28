module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearExtensionCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsTwoCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearCubic

/-!
# The cubic extension from the corrected secondary source record

The cubic constructed in O₂,Z(K) acts faithfully on the source root. Since
K_Z centralizes that root, the cubic lies outside K_Z. In the extension
K_Z X, its index-three component has the same two-core as the whole group.
After quotienting by this core, the component is the marked PSL₃(4).

The full cubic-rank bound makes the component action faithful: its kernel
has order dividing three, while its centralizer has order prime to three.
The actual cubic automorphism is inner-diagonal, so the image is PGL₃(4).
The resulting surjection and quotient isomorphism retain the inclusion of
K_Z and its original quotient marking. In particular the denominator is
the mapped intrinsic O₂(K_Z), with no extra central quotient.

This supplies the group-extension step for SecondarySourceData on printed p.618 using the original
source cubic, without identifying it with the torus. It does not select a
representation extension from its PSL₃ restriction. Construction of MSData and SecondarySourceData,
and the terminal representation contradiction remain with the source owner
`qt-d-1222-rankone-uniqueness-nonblock`.

Source: Aschbacher--Smith, conclusion of original 4.3.2, pp.618--619;
A.3.18, pp.51--53, for the cubic-rank automorphism argument.
-/

open CFSG.Quasithin Subgroup Theory.GroupTheory
open Theory.GroupAction.ComponentRankAction
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
variable {F : Type*} [Field F] [Finite F]

open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- The literal K_Z X inside the original root normalizer. -/
abbrev cubicExtension (s : SecondarySourceData c 2) (X : Subgroup G) :
    Subgroup (rootNormalizer c) := s.component ⊔ X.subgroupOf (rootNormalizer c)

/-- The original component inclusion into the cubic extension. -/
def cubicComponentInclusion (s : SecondarySourceData c 2) (X : Subgroup G) :
    s.component →* cubicExtension s X := inclusion le_sup_left

/-- A faithful root cubic produces PGL₃(4) with kernel exactly the original
component two-core. This uses the actual cubic, with no torus membership. -/
theorem cubic_extension_model (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 CFSG.KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4) (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (hX : Nat.card X = 3) (hXr : X ≤ rootNormalizer c)
    (hfaith : X ⊓ centralizer (root c : Set G) = ⊥) :
    ∃ φ : cubicExtension s X →* Matrix.ProjGenLinGroup (Fin 3) F,
      Function.Surjective φ ∧
      φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
      pCore 2 (cubicExtension s X) = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
      ∀ b : s.component, φ (cubicComponentInclusion s X b) =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (e (QuotientGroup.mk' (pCore 2 s.component) b)) := by
  let E := cubicExtension s X
  let B := s.component.subgroupOf E
  let := s.normal
  let eB : B ≃* s.component := subgroupOfEquivOfLe (show s.component ≤ E from le_sup_left)
  let eqB := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let eb := eqB.trans e
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqB.symm
  have hB : B.IsCComponent := s.isComponent.subgroupOf le_sup_left
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  have hxG : orderOf (x : G) = 3 := (orderOf_injective X.subtype X.subtype_injective x).trans hx
  let xr : rootNormalizer c := ⟨x,hXr x.property⟩
  have hxR : orderOf xr = 3 :=
    (orderOf_injective (rootNormalizer c).subtype (rootNormalizer c).subtype_injective xr).symm.trans hxG
  have hgenX : zpowers (x : G) = X := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    rw [Nat.card_zpowers, hxG, hX]
  have hgenR : zpowers xr = X.subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [MonoidHom.map_zpowers, map_subgroupOf_eq_of_le hXr]
    exact hgenX
  let a : E := ⟨xr, (le_sup_right : X.subgroupOf (rootNormalizer c) ≤ E) x.property⟩
  have ha : orderOf a = 3 :=
    (orderOf_injective E.subtype E.subtype_injective a).symm.trans hxR
  have haB : a ∉ B := by
    intro hb
    have hb' : (x : G) ∈ s.component.map (rootNormalizer c).subtype := ⟨xr,hb,rfl⟩
    have hx1 : (x : G) = 1 := mem_bot.mp (hfaith.le
      ⟨x.property, (EndgameSieve.SecondarySourceData.component_centralizes_root s) hb'⟩)
    rw [hx1, orderOf_one] at hxG
    norm_num at hxG
  have hgen : B ⊔ zpowers a = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    change s.component ⊔ zpowers xr = E
    rw [hgenR]
  obtain ⟨φ,hφ,hker,hcore,hmark⟩ := cubic_extension_of_normal_component ((rootNormalizer_sqtk c D h).subgroup E)
    hB hF eb a ha haB hgen
  have hmap : B.pCoreIn 2 = (pCore 2 s.component).map (cubicComponentInclusion s X) := by
    change (pCore 2 B).map B.subtype = _
    rw [← pCore_map_iso 2 eB, map_map]
    rfl
  refine ⟨φ,hφ,hker.trans hmap,hcore.trans hmap,?_⟩
  intro b
  have hm := hmark (eB.symm b)
  change φ (cubicComponentInclusion s X b) = _ at hm
  exact hm

omit [Finite G] [Finite F] in
/-- The marked PGL extension induces exactly the original action on the full
component quotient. This equation retains both subgroup inclusions. -/
theorem cubic_extension_action (s : SecondarySourceData c 2)
    (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) (X : Subgroup G)
    (φ : cubicExtension s X →* Matrix.ProjGenLinGroup (Fin 3) F)
    (hmark : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (e (QuotientGroup.mk' (pCore 2 s.component) b)))
    (g : cubicExtension s X) (z : s.component ⧸ pCore 2 s.component) :
    e (s.action g z) = (pglEquivInnerDiagonal F (φ g)).val (e z) := by
  let := s.normal
  let q := QuotientGroup.mk' (pCore 2 s.component)
  let ψ : cubicExtension s X →* MulAut PSL(3,F) :=
    (Matrix.PSL3.OuterSolvable.innerDiagonal F).subtype.comp
      ((pglEquivInnerDiagonal F).toMonoidHom.comp φ)
  have hm (b : s.component) : ψ (cubicComponentInclusion s X b) = MulAut.conj (e (q b)) := by
    change (pglEquivInnerDiagonal F (φ (cubicComponentInclusion s X b))).val = _
    rw [hmark, pglEquiv_component]
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hb : cubicComponentInclusion s X (MulAut.conjNormal (g : rootNormalizer c) b) =
      g * cubicComponentInclusion s X b * g⁻¹ := by
    apply Subtype.ext
    rfl
  have he := congrArg ψ hb
  rw [hm, map_mul, map_mul, map_inv, hm] at he
  change e (normalQuotientAction s.component (pCore 2 s.component)
    (g : rootNormalizer c) (q b)) = ψ g (e (q b))
  rw [normalQuotientAction_apply_mk]
  apply inner_injective F
  rw [he]
  ext x
  simp

/-- The source choice in O₂,Z(K) gives the actual PGL₃(4) extension, with
its exact kernel and component projection. The MS and secondary constructions
remain with the enclosing nonblock source assembly. -/
theorem exists_source_cubic_extension (d : MSData c 2)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4) (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ X ⊓ s.component.map (rootNormalizer c).subtype = ⊥ ∧
      Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅Q c,X⁆ = Q c ∧
      ∃ φ : cubicExtension s X →* Matrix.ProjGenLinGroup (Fin 3) F,
        Function.Surjective φ ∧
        φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        pCore 2 (cubicExtension s X) =
          (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        (∀ b : s.component, φ (cubicComponentInclusion s X b) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (e (QuotientGroup.mk' (pCore 2 s.component) b))) ∧
        ∀ (g : cubicExtension s X) (z : s.component ⧸ pCore 2 s.component),
          e (s.action g z) = (pglEquivInnerDiagonal F (φ g)).val (e z) := by
  obtain ⟨X,hX,hXK,hXr,hfix,hfaith,_,_,hcomm,hmoved,_⟩ :=
    d.exists_source_cubic_root D
  have hdisj : X ⊓ s.component.map (rootNormalizer c).subtype = ⊥ :=
    bot_unique ((inf_le_inf_left _
      (EndgameSieve.SecondarySourceData.component_centralizes_root s)).trans_eq hfaith)
  obtain ⟨φ,hφ,hker,hcore,hmark⟩ := cubic_extension_model s D h hF e X hX hXr hfaith
  exact ⟨X,hX,hXK,hXr,hdisj,hfix,hcomm,hmoved,φ,hφ,hker,hcore,hmark,
    cubic_extension_action s e X φ hmark⟩

/-- The quotient is by the mapped intrinsic O₂(K_Z), with the original
component marking. No additional central or prime-to-three quotient occurs. -/
theorem cubic_extension_quotient (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4) (e : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (hX : Nat.card X = 3) (hXr : X ≤ rootNormalizer c)
    (hfaith : X ⊓ centralizer (root c : Set G) = ⊥) :
    ∃ E : (cubicExtension s X ⧸ pCore 2 (cubicExtension s X)) ≃*
        Matrix.ProjGenLinGroup (Fin 3) F,
      (pCore 2 (cubicExtension s X)).map (cubicExtension s X).subtype =
        (pCore 2 s.component).map s.component.subtype ∧
      ∀ b : s.component,
        E (QuotientGroup.mk' _ (cubicComponentInclusion s X b)) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (e (QuotientGroup.mk' (pCore 2 s.component) b)) := by
  obtain ⟨φ,hφ,hker,hcore,hmark⟩ := cubic_extension_model s D h hF e X hX hXr hfaith
  have hk : pCore 2 (cubicExtension s X) = φ.ker := hcore.trans hker.symm
  let E := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  refine ⟨E, ?_, ?_⟩
  · rw [hcore, map_map]
    rfl
  · exact hmark

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
end
