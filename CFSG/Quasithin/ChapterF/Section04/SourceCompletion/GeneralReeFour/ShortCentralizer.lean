module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.OuterSylow

/-!
# Full short-root centralizers in the marked general Ree extension

The nonidentity native two-subgroup fixes a tree in the native octagon.
The exact native-to-extension graph isomorphism lets its full extension
normalizer act on this same tree. Every color-preserving automorphism fixes
its center, so a native conjugator puts the whole extension normalizer in
one of the original extension endpoints. No ambient generation is assumed.

For a short-root involution, the embedded PSL₂ subgroup excludes the
Suzuki endpoint. The native centralizer is therefore in the linear
parabolic, and its central involution lies in the actual linear radical.
The full extension centralizer, including every outer element, lies in
that same marked left endpoint. This supplies the native/extension half
of F.4.42; the original ambient centralizer still requires its source proof.
Source: Aschbacher–Smith F.4.27(4)(ii),42–43, printed pp.288,295–296;
GLS3 Theorem 3.1.3 (`refs/quasithin.pdf`, `refs/KGroup/GLS3/chapter3.tex`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
open SimpleGraph GroupAction.EvenPolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.EvenInvolutionGeometry
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

private def reindexCoset {N I J : Type*} [Group N]
    (F : I → Subgroup N) (e : I ≃ J) (i : I) :
    N ⧸ F i → N ⧸ F (e.symm (e i)) :=
  Quotient.map id (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    change a⁻¹ * b ∈ F (e.symm (e i))
    rw [e.symm_apply_apply]
    exact QuotientGroup.leftRel_apply.mp h)

private def reindexVertex {N I J : Type*} [Group N]
    (F : I → Subgroup N) (e : I ≃ J) (v : CosetGeometry.Vertex F) :
    CosetGeometry.Vertex (fun j => F (e.symm j)) :=
  ⟨e v.type,reindexCoset F e v.type v.coset⟩

private theorem reindexVertex_mk {N I J : Type*} [Group N]
    (F : I → Subgroup N) (e : I ≃ J) (i : I) (g : N) :
    reindexVertex F e ⟨i,g⟩ = ⟨e i,g⟩ := rfl

private theorem reindexVertex_smul {N I J : Type*} [Group N]
    (F : I → Subgroup N) (e : I ≃ J) (g : N) (v : CosetGeometry.Vertex F) :
    reindexVertex F e (g • v) = g • reindexVertex F e v := by
  rcases v with ⟨i,q⟩
  obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
  rfl

private theorem reindex_exists {N I J : Type*} [Group N]
    (F : I → Subgroup N) (e : I ≃ J) :
    ∃ f : Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.graph F ≃g
        Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.graph (fun j => F (e.symm j)),
      (∀ v, (f v).type = e v.type) ∧ ∀ (g : N) v, f (g • v) = g • f v := by
  have hi : Function.Injective (reindexVertex F e) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    have hij : i = j := e.injective (congrArg CosetGeometry.Vertex.type h)
    subst j
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective b
    have hh : (a : N ⧸ F (e.symm (e i))) = b := by
      simpa only [reindexVertex_mk,CosetGeometry.Vertex.mk.injEq,heq_eq_eq,true_and] using h
    apply congrArg (CosetGeometry.Vertex.mk i)
    apply QuotientGroup.eq.mpr
    have hh' := QuotientGroup.eq.mp hh
    rwa [e.symm_apply_apply] at hh'
  have hs : Function.Surjective (reindexVertex F e) := by
    rintro ⟨j,q⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨e.symm j,a⟩,?_⟩
    rw [reindexVertex_mk]
    exact congrArg (fun j => (⟨j,(a : N)⟩ : CosetGeometry.Vertex (fun j => F (e.symm j))))
      (e.apply_symm_apply j)
  let f : CosetGeometry.Vertex F ≃ CosetGeometry.Vertex (fun j => F (e.symm j)) :=
    Equiv.ofBijective (reindexVertex F e) ⟨hi,hs⟩
  have hinc (v w : CosetGeometry.Vertex F) :
      Incident (fun j => F (e.symm j)) (f v) (f w) ↔ Incident F v w := by
    constructor
    · rintro ⟨g,hg,hg'⟩
      refine ⟨g,?_,?_⟩
      · have hh : f ⟨v.type,g⟩ = f v := by
          change CosetGeometry.Vertex.mk (e v.type) _ = _
          exact congrArg (CosetGeometry.Vertex.mk (e v.type)) hg
        have hh' := hi hh
        cases v with
        | mk i q => simpa only [CosetGeometry.Vertex.mk.injEq,heq_eq_eq,true_and] using hh'
      · have hh : f ⟨w.type,g⟩ = f w := by
          change CosetGeometry.Vertex.mk (e w.type) _ = _
          exact congrArg (CosetGeometry.Vertex.mk (e w.type)) hg'
        have hh' := hi hh
        cases w with
        | mk i q => simpa only [CosetGeometry.Vertex.mk.injEq,heq_eq_eq,true_and] using hh'
    · rintro ⟨g,hg,hg'⟩
      refine ⟨g,?_,?_⟩
      · exact congrArg (reindexCoset F e v.type) hg
      · exact congrArg (reindexCoset F e w.type) hg'
  refine ⟨⟨f,?_⟩,fun _ => rfl,reindexVertex_smul F e⟩
  intro v w
  change (e v.type ≠ e w.type ∧ _) ↔ (v.type ≠ w.type ∧ _)
  exact and_congr (not_congr e.injective.eq_iff) (hinc v w)

private def sideBool : Side ≃ Bool where
  toFun s := match s with | .linear => false | .suzuki => true
  invFun b := if b then .suzuki else .linear
  left_inv := by intro s; cases s <;> rfl
  right_inv := by intro b; cases b <;> rfl

private theorem native_graph_comparison (m : ℕ) :
    ∃ f : incidenceGraph m ≃g CosetGeometry.RankTwo.graph (ReeF4.SourceCompletion.family m),
      (∀ v, (f v).type = sideBool v.type) ∧ ∀ (g : Model m) v, f (g • v) = g • f v := by
  have hf : (fun b => ConverseParabolics.parabolic m (sideBool.symm b)) =
      ReeF4.SourceCompletion.family m := by
    funext b
    cases b <;> exact parabolic_eq_rootParabolic m _
  rw [←hf]
  exact reindex_exists (ConverseParabolics.parabolic m) sideBool

variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

/-- The normalizer in the full extension fixes a native vertex for each nonidentity native two-subgroup. -/
theorem extension_normalizer_fixed_vertex (hm : 0 < m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ v : CosetGeometry.Vertex E.family,
      ∀ a ∈ normalizer (R.map E.baseHom : Set E.carrier), a • v = v := by
  obtain ⟨f,hft,hfs⟩ := native_graph_comparison m
  have hi := ReeF4.SmallCompletion.conj_injective m hm
  let e := f.trans (E.graphIso hi)
  have et (v) : (e v).type = sideBool v.type := hft v
  have es (g : Model m) (v) : e (g • v) = E.baseHom g • e v := by
    exact (congrArg (E.vertexMap hi) (hfs g v)).trans (E.vertexMap_smul hi g (f v))
  have fix (v) : v ∈ fixedVertices R ↔ e v ∈ fixedVertices (R.map E.baseHom) := by
    constructor
    · intro hv a ha
      obtain ⟨r,hr,rfl⟩ := ha
      rw [←es,hv r hr]
    · intro hv r hr
      exact e.injective ((es r v).trans (hv _ (mem_map_of_mem _ hr)))
  let T := (incidenceGraph m).induce (fixedVertices R)
  have hT : T.IsTree := fixed_graph_isTree
    ((octagonGeometry m hm).toEvenPolygonAction (oddApartmentStabilizers m hm))
    R hR hp (ConverseParabolics.twoSubgroup_fixes_edge R hp)
  obtain ⟨v,hv⟩ := hT.exists_fixed_vertex_of_color_preserving
    (fun x => vertexColor x.val) (fun h => adjacent_color h)
  have hpull (a : E.carrier) (ha : a ∈ normalizer (R.map E.baseHom : Set E.carrier))
      (w : MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.Vertex m)
      (hw : w ∈ fixedVertices R) :
      e.symm (a • e w) ∈ fixedVertices R := by
    apply (fix _).mpr
    rw [e.apply_symm_apply]
    exact normalizer_smul_mem_fixedVertices _ ha ((fix w).mp hw)
  have hcolor (a : E.carrier) (w) : vertexColor (e.symm (a • e w)) = vertexColor w := by
    have ht : (e.symm (a • e w)).type = w.type := by
      apply sideBool.injective
      rw [←et,e.apply_symm_apply]
      exact et w
    change (match (e.symm (a • e w)).type with | .suzuki => false | .linear => true) = _
    rw [ht]
    rfl
  refine ⟨e v.val,?_⟩
  intro a ha
  let b : T ≃g T := {
    toEquiv := {
      toFun := fun w => ⟨e.symm (a • e w.val),hpull a ha w.val w.property⟩
      invFun := fun w => ⟨e.symm (a⁻¹ • e w.val),hpull a⁻¹
        ((normalizer (R.map E.baseHom : Set E.carrier)).inv_mem ha) w.val w.property⟩
      left_inv := by intro w; apply Subtype.ext; simp only [e.apply_symm_apply,inv_smul_smul,e.symm_apply_apply]
      right_inv := by intro w; apply Subtype.ext; simp only [e.apply_symm_apply,smul_inv_smul,e.symm_apply_apply] }
    map_rel_iff' := by
      intro w u
      change (incidenceGraph m).Adj (e.symm (a • e w.val)) (e.symm (a • e u.val)) ↔ _
      rw [e.symm.map_rel_iff]
      exact (CosetGeometry.translationGraphIso E.family a).map_rel_iff.trans e.map_rel_iff }
  have hh := congrArg (fun w : fixedVertices R => e w.val) (hv b (fun w => hcolor a w.val))
  change e (e.symm (a • e v.val)) = e v.val at hh
  rwa [e.apply_symm_apply] at hh

/-- Normalizer coverage uses a native conjugator and the same full extension endpoints. -/
theorem extension_native_normalizer_cover (hm : 0 < m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ∃ (g : Model m) (i : Bool),
      (normalizer (R.map E.baseHom : Set E.carrier)).map
        (MulAut.conj (E.baseHom g)).toMonoidHom ≤ E.family i := by
  obtain ⟨v,hv⟩ := extension_normalizer_fixed_vertex E hm R hR hp
  obtain ⟨a,ha⟩ := CosetGeometry.exists_smul_base E.family v
  obtain ⟨g,hg⟩ := E.exists_native_representative a
  have hgv : E.baseHom g • CosetGeometry.base E.family v.type = v := by
    calc
      E.baseHom g • CosetGeometry.base E.family v.type =
          a • CosetGeometry.base E.family v.type := by
        change CosetGeometry.Vertex.mk v.type _ = CosetGeometry.Vertex.mk v.type _
        apply congrArg (CosetGeometry.Vertex.mk v.type)
        change (↑(E.baseHom g * 1) : E.carrier ⧸ E.family v.type) = ↑(a * 1)
        simpa only [mul_one] using hg v.type
      _ = v := ha
  refine ⟨g⁻¹,v.type,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  have hh : (E.baseHom g)⁻¹ * b * E.baseHom g ∈
      MulAction.stabilizer E.carrier (CosetGeometry.base E.family v.type) := by
    change ((E.baseHom g)⁻¹ * b * E.baseHom g) • CosetGeometry.base E.family v.type = _
    rw [mul_smul,mul_smul,hgv,hv b hb,←hgv,inv_smul_smul]
    rfl
  rw [CosetGeometry.stabilizer_base] at hh
  change E.baseHom g⁻¹ * b * (E.baseHom g⁻¹)⁻¹ ∈ E.family v.type
  rwa [map_inv,inv_inv]

/-- A short-root representative in the literal linear radical has its entire centralizer in this same extension's left endpoint. -/
theorem extension_short_centralizer_placement (hm : 0 < m)
    (a : CoefficientField m) (ha : a ≠ 0) :
    ∃ t : Model m, IsConj (shortRootElement m a) t ∧ orderOf t = 2 ∧
      t ∈ radical m .linear ∧
      centralizer ({t} : Set (Model m)) ≤ parabolic m .linear ∧
      centralizer ({E.baseHom t} : Set E.carrier) ≤ E.left.subgroupOf E.carrier := by
  let u := shortRootElement m a
  have hu : orderOf u = 2 := shortRootElement_orderOf m ha
  have hne : zpowers u ≠ ⊥ := by
    intro h
    have he := zpowers_eq_bot.mp h
    simp [he] at hu
  have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hu,pow_one])
  obtain ⟨g,i,hg⟩ := extension_native_normalizer_cover E hm (zpowers u) hne hp
  let t := (MulAut.conj g) u
  have ht : IsShortRootInvolution t := ⟨a,ha,isConj_iff.mpr ⟨g,rfl⟩⟩
  have hCN : centralizer ({E.baseHom u} : Set E.carrier) ≤
      normalizer ((zpowers u).map E.baseHom : Set E.carrier) := by
    rw [MonoidHom.map_zpowers,←centralizer_closure ({E.baseHom u} : Set E.carrier),
      ←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hC : centralizer ({E.baseHom t} : Set E.carrier) ≤ E.family i := by
    have hh := (map_mono hCN (f := (MulAut.conj (E.baseHom g)).toMonoidHom)).trans hg
    rw [CentralizerSmallKernelTransport.map_centralizer] at hh
    have he : (MulAut.conj (E.baseHom g)) (E.baseHom u) = E.baseHom t := by
      change E.baseHom g * E.baseHom u * (E.baseHom g)⁻¹ = E.baseHom (g*u*g⁻¹)
      rw [map_mul,map_mul,map_inv]
    rwa [he] at hh
  have hnative : centralizer ({t} : Set (Model m)) ≤
      UnitaryNonbinary.SourceExtension.nativeFamily
        (P₀ := parabolic m .linear) (P₁ := parabolic m .suzuki) i := by
    intro x hx
    apply (E.baseHom_mem_family_iff (ReeF4.SmallCompletion.conj_injective m hm) i x).mp
    apply hC
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x t from mem_centralizer_singleton_iff.mp hx).map E.baseHom).eq
  have hi : i = false := by
    cases i
    · rfl
    · have h3 := (ReeF4.SourceCompletion.short_centralizer_residual_three_dvd hm ht).trans
        ((card_subgroup_dvd_card _).trans (card_dvd_of_le hnative))
      change 3 ∣ Nat.card (parabolic m .suzuki) at h3
      rw [←parabolic_eq_rootParabolic] at h3
      exact (ConverseParabolics.suzuki_parabolic_three_free hm h3).elim
  subst i
  exact ⟨t,isConj_iff.mpr ⟨g,rfl⟩,orderOf_of_isShortRootInvolution ht,
    ReeF4.SourceCompletion.short_mem_radical_of_centralizer_le hm ht hnative,hnative,hC⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
