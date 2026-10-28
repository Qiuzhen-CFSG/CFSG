module
public import Theory.Representation.BinaryOffender.TwoFixedSpaces
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.TwoConjugates
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# The conjugate-span consequence of the sharp two-conjugate argument

The fixed spaces of J and one residual conjugate span the actual binary
module at the sharp codimension bound. If its J-fixed subgroup lies in E,
the residual orbit of E therefore contains the module. The alpha identity
then identifies that orbit as the module times C_E(O²(H)). Applying this to
the actual moved subgroup gives the literal final identity of E.2.3(2).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G D : Type*} [Group G] [Finite G] [Group D]

theorem fixed_subgroups_generate_of_codim_sum
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (A B L : Subgroup G)
    (hgen : L.map q ≤ A.map q ⊔ B.map q)
    (hcod : fixedCodim U A + fixedCodim U B ≤ fixedCodim U L) :
    (U ⊓ centralizer (A : Set G)) ⊔ (U ⊓ centralizer (B : Set G)) = U := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hd : BinaryOffender.fixedCodim ρ (A.map q) +
      BinaryOffender.fixedCodim ρ (B.map q) ≤ BinaryOffender.fixedCodim ρ (L.map q) := by
    simpa only [fixedCodim_eq_centralizer_quotient U q hq hker] using hcod
  have hs := BinaryOffender.fixedSpace_sup_eq_top_of_codim_sum
    ρ (A.map q) (B.map q) (L.map q) hgen hd
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  have hv : Additive.ofMul (⟨x,hx⟩ : U) ∈
      BinaryOffender.fixedSpace ρ (A.map q) ⊔ BinaryOffender.fixedSpace ρ (B.map q) :=
    hs.symm ▸ Submodule.mem_top
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
  have ha' := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker A a).mp ha
  have hb' := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker B b).mp hb
  have he' := congrArg (fun v : Additive U => (v.toMul:G)) he
  change (a.toMul:G) * (b.toMul:G) = x at he'
  rw [← he']
  exact mul_mem_sup ⟨a.toMul.property,ha'⟩ ⟨b.toMul.property,hb'⟩

omit [Finite G] in
theorem conjugateSpan_eq_of_two_fixed_subgroups
    (U E A L : Subgroup G) [U.Normal]
    (g : G) (hg : g ∈ L)
    (hfixed : (U ⊓ centralizer (A : Set G)) ⊔
      (U ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)) = U)
    (hE : E = (U ⊓ centralizer (A : Set G)) ⊔ (E ⊓ centralizer (L : Set G))) :
    conjugateSpanBy E L = U ⊔ (E ⊓ centralizer (L : Set G)) := by
  have hUE : U ⊓ centralizer (A : Set G) ≤ E := hE ▸ le_sup_left
  have hm : (U ⊓ centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom =
      U ⊓ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hu : U.map (MulAut.conj g).toMonoidHom = U := Normal.map_conj_eq U g
    rw [map_inf _ _ _ (MulAut.conj g).injective, hu, map_centralizer_equiv]
    rfl
  have hUF : U ≤ conjugateSpanBy E L := by
    rw [← hfixed]
    apply sup_le (hUE.trans (le_conjugateSpanBy E L))
    rw [← hm]
    rintro _ ⟨x,hx,rfl⟩
    exact subset_closure ⟨g,hg,x,hUE hx,rfl⟩
  apply le_antisymm ?_ (sup_le hUF (inf_le_left.trans (le_conjugateSpanBy E L)))
  apply conjugateSpanBy_le
  · exact hE.le.trans (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
  · have hC : L ≤ centralizer (E ⊓ centralizer (L : Set G) : Set G) :=
      le_centralizer_iff.mp inf_le_right
    have hNU : L ≤ normalizer (U : Set G) := le_normalizer_of_normal
    have hNC : L ≤ normalizer (E ⊓ centralizer (L : Set G) : Set G) :=
      hC.trans (centralizer_le_normalizer _)
    exact (le_inf hNU hNC).trans
      (normalizer_inf_normalizer_le_normalizer_sup U (E ⊓ centralizer (L : Set G)))

theorem thompsonAlpha_span_of_two_conjugates
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (g : G) (hg : g ∈ pResidual 2 G)
    (hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q)
    (hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G))
    (hE : thompsonAlpha (T : Subgroup G) =
      (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G))) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  apply conjugateSpan_eq_of_two_fixed_subgroups U _ _ _ g hg ?_ hE
  apply fixed_subgroups_generate_of_codim_sum U q hq hker _ _ _ hgen
  simpa only [fixedCodim_conjugate,two_mul] using hcod
/-- The exact orbit identity also gives alpha in the source's moved-module form. -/
theorem thompsonAlpha_decomposition_of_orbit_span
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUT : U ≤ T) (L : Subgroup G)
    (hspan : conjugateSpanBy (thompsonAlpha (T : Subgroup G)) L =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G))) :
    thompsonAlpha (T : Subgroup G) =
      (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have hEU : thompsonAlpha (T : Subgroup G) ≤
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) :=
    (le_conjugateSpanBy _ _).trans_eq hspan
  have hfixed := alpha_inf_eq_fixed U (T : Subgroup G) hUT
  apply le_antisymm ?_ (sup_le (hfixed.ge.trans inf_le_left) inf_le_left)
  intro x hx
  obtain ⟨u,hu,c,hc,he⟩ := mem_sup_of_normal_left.mp (hEU hx)
  have hue : u ∈ thompsonAlpha (T : Subgroup G) := by
    have huc : u = x*c⁻¹ := by rw [← he]; simp
    rw [huc]
    exact mul_mem hx (inv_mem hc.1)
  rw [← he]
  exact mul_mem_sup (hfixed.le ⟨hue,hu⟩) hc

end CFSG.Quasithin.ChapterB.RankOneBaumann
