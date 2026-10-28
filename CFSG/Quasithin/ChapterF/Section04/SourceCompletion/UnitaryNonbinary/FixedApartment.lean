module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.NativeWeyl
public import Theory.GroupAction.DihedralPolygon.FixedQuadrangle
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Geometry

/-!
# Native fixed neighbors and full-extension apartment closure

Inner-times-middle factorization provides native representatives for all
neighbors in the full extension geometry. The literal whole-overlap equality
then transfers a native torus fixed-coset calculation to those neighbors.
Short geodesics preserve torus fixation, and the quadrangle metric closes
the resulting thin dihedral arc after eight edges.

The conclusion is membership of the fourth rotation power in the full
middle. It does not identify the full middle with its native subgroup or
eliminate an outer defect. The concrete four- and five-dimensional consumers
discharge all native fixed-coset and reflection premises.

Source: Aschbacher–Smith F.4.10,13,16–17, printed pp.279–283 of
`refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {B : Type*} [Group B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁) {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

def nativeMap : (i : Bool) → nativeFamily (P₀ := P₀) (P₁ := P₁) i →* M
  | false => E.innerLeft c
  | true => E.innerRight c

private theorem nativeMap_mem (i : Bool) (g : nativeFamily (P₀ := P₀) (P₁ := P₁) i) :
    E.nativeMap c i g ∈ c.cosetFamily i := by
  cases i <;> exact ⟨_,rfl⟩

private theorem overlap_le (i : Bool) : P₀ ⊓ P₁ ≤ nativeFamily (P₀ := P₀) (P₁ := P₁) i := by
  cases i
  · exact inf_le_left
  · exact inf_le_right

theorem nativeMap_middle (i : Bool) (g : (P₀ ⊓ P₁ : Subgroup B)) :
    E.nativeMap c i ⟨g.val,by cases i; exact g.property.1; exact g.property.2⟩ = E.innerMiddle c g := by
  cases i
  · rfl
  · exact (E.innerMiddle_right c g).symm

theorem nativeMap_mem_middle (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (i : Bool) (g : nativeFamily (P₀ := P₀) (P₁ := P₁) i) :
    E.nativeMap c i g ∈ c.middle.range ↔ g.val ∈ P₀ ⊓ P₁ := by
  constructor
  · rintro ⟨b,hb⟩
    have he : MulAut.conj g.val=b.val := by
      cases i
      · exact (congrArg Subtype.val (c.left_injective hb)).symm
      · exact (congrArg Subtype.val (c.right_injective
          ((DFunLike.congr_fun c.compatible b).symm.trans hb))).symm
    have hm : MulAut.conj g.val ∈ E.middle ⊓ inner B := ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨u,hu,he'⟩ := (E.middle_inner hi).le hm
    exact hi he' ▸ hu
  · intro hg
    rw [show E.nativeMap c i g=E.innerMiddle c ⟨g.val,hg⟩ from E.nativeMap_middle c i ⟨g.val,hg⟩]
    exact ⟨_,rfl⟩

private theorem fixes_base (g : M) (i : Bool) :
    g • base c.cosetFamily i=base c.cosetFamily i ↔ g∈c.cosetFamily i := by
  change g∈MulAction.stabilizer M (base c.cosetFamily i) ↔ _
  rw [base,Subgroup.CosetGeometry.stabilizer_base]

private theorem middle_fixes (a : E.middle) (i : Bool) :
    c.middle a • base c.cosetFamily i=base c.cosetFamily i := by
  apply (E.fixes_base c _ i).mpr
  cases i
  · exact c.middle_le_left ⟨a,rfl⟩
  · exact c.middle_le_right ⟨a,rfl⟩

/-- Every neighbor has a native representative, even for a full extension. -/
theorem neighbor_native_rep (hi : Function.Injective (MulAut.conj : B →* MulAut B)) (i : Bool) (v : Vertex c.cosetFamily)
    (hv : (graph c.cosetFamily).Adj (base c.cosetFamily i) v) :
    ∃ g : nativeFamily (P₀ := P₀) (P₁ := P₁) i,
      E.nativeMap c i g • base c.cosetFamily (!i)=v := by
  obtain ⟨a,ha,he⟩ := neighbor_base_rep c.cosetFamily i hv
  have he' : a • base c.cosetFamily (!i)=v := by
    change mkVertex c.cosetFamily (!i) (a*1)=v
    simpa only [mul_one] using he
  cases i
  · obtain ⟨u,rfl⟩ := ha
    obtain ⟨g,hg,b,hb,hu⟩ := E.left_factor hi u.val u.property
    have hu' : u=E.nativeLeft ⟨g,hg⟩*E.amalgam.left ⟨b,hb⟩ := Subtype.ext hu
    refine ⟨⟨g,hg⟩,?_⟩
    rw [hu',map_mul,mul_smul] at he'
    change E.innerLeft c ⟨g,hg⟩ • (c.middle ⟨b,hb⟩ • base c.cosetFamily (!false))=v at he'
    rw [middle_fixes] at he'
    exact he'
  · obtain ⟨u,rfl⟩ := ha
    obtain ⟨g,hg,b,hb,hu⟩ := E.right_factor hi u.val u.property
    have hu' : u=E.nativeRight ⟨g,hg⟩*E.amalgam.right ⟨b,hb⟩ := Subtype.ext hu
    have hright : c.right (E.amalgam.right ⟨b,hb⟩)=c.middle ⟨b,hb⟩ :=
      (DFunLike.congr_fun c.compatible ⟨b,hb⟩).symm
    refine ⟨⟨g,hg⟩,?_⟩
    rw [hu',map_mul,hright,mul_smul,middle_fixes] at he'
    exact he'

variable {T : Type*} (torus : T → (P₀ ⊓ P₁ : Subgroup B))
def TorusFixed (v : Vertex c.cosetFamily) : Prop := ∀ p, E.innerMiddle c (torus p) • v=v

/-- The native fixed-coset calculation transfers through the whole overlap. -/
theorem torus_fixed_neighbors
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (i : Bool) (s : nativeFamily (P₀ := P₀) (P₁ := P₁) i) (hs : s^2=1)
    (hf : ∀ g : nativeFamily (P₀ := P₀) (P₁ := P₁) i,
      (∀ p, g.val⁻¹*(torus p).val*g.val ∈ P₀ ⊓ P₁) →
        g.val∈P₀ ⊓ P₁ ∨ (s*g).val∈P₀ ⊓ P₁)
    (v : Vertex c.cosetFamily) (hv : (graph c.cosetFamily).Adj (base c.cosetFamily i) v)
    (hfixed : E.TorusFixed c torus v) :
    v=base c.cosetFamily (!i) ∨ v=E.nativeMap c i s • base c.cosetFamily (!i) := by
  obtain ⟨g,rfl⟩ := E.neighbor_native_rep c hi i v hv
  have hh (p : T) : g.val⁻¹*(torus p).val*g.val∈P₀ ⊓ P₁ := by
    let z : nativeFamily (P₀ := P₀) (P₁ := P₁) i := ⟨(torus p).val,overlap_le i (torus p).property⟩
    have hconj : E.nativeMap c i (g⁻¹*z*g) • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
      have h := hfixed p
      rw [←E.nativeMap_middle c i (torus p)] at h
      simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using congrArg ((E.nativeMap c i g)⁻¹ • ·) h
    apply (E.nativeMap_mem_middle c hi i (g⁻¹*z*g)).mp
    rw [←ho]
    have hown := E.nativeMap_mem c i (g⁻¹*z*g)
    have hother := (E.fixes_base c _ (!i)).mp hconj
    cases i
    · exact ⟨hown,hother⟩
    · exact ⟨hother,hown⟩
  have fixes {u : nativeFamily (P₀ := P₀) (P₁ := P₁) i} (hu : u.val∈P₀ ⊓ P₁) :
      E.nativeMap c i u • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
    obtain ⟨b,hb⟩ := (E.nativeMap_mem_middle c hi i u).mpr hu
    rw [←hb]
    exact E.middle_fixes c b (!i)
  rcases hf g hh with h | h
  · exact Or.inl (fixes h)
  · right
    have h2 : E.nativeMap c i s*E.nativeMap c i s=1 := by rw [←map_mul,←pow_two,hs,map_one]
    have h' := congrArg (E.nativeMap c i s • ·) (fixes h)
    rw [map_mul,mul_smul,←mul_smul,h2,one_smul] at h'
    exact h'

private theorem torus_fixed_base (i : Bool) : E.TorusFixed c torus (base c.cosetFamily i) := by
  intro p
  exact E.middle_fixes c (E.nativeMiddle (torus p)) i

private theorem torus_fixed_reflection
    (i : Bool) (s : nativeFamily (P₀ := P₀) (P₁ := P₁) i) (hs : s^2=1)
    (hn : ∀ p, ∃ q, s.val*(torus p).val*s.val=(torus q).val)
    (v : Vertex c.cosetFamily) :
    E.TorusFixed c torus (E.nativeMap c i s • v) ↔ E.TorusFixed c torus v := by
  let u := E.nativeMap c i s
  have huu : u*u=1 := by dsimp [u]; rw [←map_mul,←pow_two,hs,map_one]
  have hrot (p : T) : ∃ q, u*E.innerMiddle c (torus p)*u=E.innerMiddle c (torus q) := by
    obtain ⟨q,hq⟩ := hn p
    refine ⟨q,?_⟩
    rw [←E.nativeMap_middle c i (torus p),←E.nativeMap_middle c i (torus q)]
    change E.nativeMap c i s * E.nativeMap c i _ * E.nativeMap c i s = _
    rw [←map_mul,←map_mul]
    exact congrArg (E.nativeMap c i) (Subtype.ext hq)
  have hf (z : Vertex c.cosetFamily) (hz : E.TorusFixed c torus z) : E.TorusFixed c torus (u • z) := by
    intro p
    obtain ⟨q,hq⟩ := hrot p
    calc
      E.innerMiddle c (torus p) • (u • z) = u • ((u*E.innerMiddle c (torus p)*u) • z) := by
        simp only [mul_smul,←mul_smul u u,huu,one_smul]
      _ = u • z := by rw [hq,hz q]
  refine ⟨fun hv => ?_,hf v⟩
  simpa only [←mul_smul,huu,one_smul] using hf (u • v) hv

/-- Native torus separation closes the marked apartment in the full geometry.
The output is full-middle membership; it does not silently identify that
middle with its smaller native subgroup. -/
theorem nativeRotation_four_mem_middle
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (s : P₀) (t : P₁) (hs : s^2=1) (ht : t^2=1)
    (hsout : s.val∉P₁) (htout : t.val∉P₀)
    (hns : ∀ p, ∃ q, s.val*(torus p).val*s.val=(torus q).val)
    (hnt : ∀ p, ∃ q, t.val*(torus p).val*t.val=(torus q).val)
    (hfs : ∀ g : P₀, (∀ p, g.val⁻¹*(torus p).val*g.val∈P₀ ⊓ P₁) →
      g.val∈P₀ ⊓ P₁ ∨ (s*g).val∈P₀ ⊓ P₁)
    (hft : ∀ g : P₁, (∀ p, g.val⁻¹*(torus p).val*g.val∈P₀ ⊓ P₁) →
      g.val∈P₀ ⊓ P₁ ∨ (t*g).val∈P₀ ⊓ P₁)
    (hdiam : ∀ v w,(graph c.cosetFamily).dist v w≤4)
    (hg : ∀ v (p : (graph c.cosetFamily).Walk v v),p.IsCycle → 8≤p.length) :
    E.nativeRotation c s t ^ 4 ∈ c.middle.range := by
  let x := base c.cosetFamily false
  let y := base c.cosetFamily true
  let a := E.innerLeft c s
  let b := E.innerRight c t
  have ha : a^2=1 := by dsimp [a]; rw [←map_pow,hs,map_one]
  have hb : b^2=1 := by dsimp [b]; rw [←map_pow,ht,map_one]
  have hax : a • x=x := (E.fixes_base c _ false).mpr ⟨_,rfl⟩
  have hby : b • y=y := (E.fixes_base c _ true).mpr ⟨_,rfl⟩
  have hay : a • y≠y := by
    intro hh
    have hm : a∈c.middle.range := ho ▸
      show a∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,(E.fixes_base c _ true).mp hh⟩
    exact hsout ((E.nativeMap_mem_middle c hi false s).mp hm).2
  have hbx : b • x≠x := by
    intro hh
    have hm : b∈c.middle.range := ho ▸
      show b∈c.left.range⊓c.right.range from ⟨(E.fixes_base c _ false).mp hh,⟨_,rfl⟩⟩
    exact htout ((E.nativeMap_mem_middle c hi true t).mp hm).1
  let D : GroupAction.DihedralPolygon.BipartiteAction M (graph c.cosetFamily) :=
    { color := (·.type), adjacent_color := fun h => h.1,
      smul_adj := fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h,
      smul_color := fun _ _ => rfl }
  have hact : GraphAction (graph c.cosetFamily) M := ⟨D.smul_adj⟩
  have hh := GroupAction.DihedralPolygon.QuadrangleApartment.fixed_edge_sequence_closes
    D a b x y ha hb hax hby
    ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩ hay hbx
    (connected c.cosetFamily c.generated) hdiam hg (E.TorusFixed c torus)
    (E.torus_fixed_base c torus false) (E.torus_fixed_base c torus true)
    (E.torus_fixed_reflection c torus false s hs hns)
    (E.torus_fixed_reflection c torus true t ht hnt)
    (E.torus_fixed_neighbors c torus hi ho false s hs hfs)
    (E.torus_fixed_neighbors c torus hi ho true t ht hft) (by
      intro v w p hp hl hv hw u hu z
      exact SimpleGraph.QuadrangleApartment.short_geodesic_fixed hg hact p hp hl _ (hv z) (hw z) u hu)
  rw [←ho]
  exact ⟨(E.fixes_base c _ false).mp hh.1,(E.fixes_base c _ true).mp hh.2⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
