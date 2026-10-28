module

public import CFSG.Quasithin.ChapterJ.Section05.Cosets
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Complete
public import Theory.GroupTheory.NormalizerInnerAutomorphisms

/-!
# The recognized source subgroup is self-normalizing

The original five-commutator Q₅ has ambient centralizer Z≤Q₅. Thus a
subgroup F containing Q₅ contains its ambient centralizer. When F is the
full binary Ree group, every automorphism is inner, so N_G(F)=F.
This discharges the normalizer escape needed in the coset argument from
the unchanged original local subgroup, without assuming a faithful coset
representation or an ambient Rudvalis isomorphism.

Source: Aschbacher–Smith J.5.3, printed p.445; the preceding centralizer
calculation is the original J.4.5 source argument.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] (d:LocalSetup G)

/-- Any recognized full-Ree subgroup containing the original Q₅ is self-normalizing. -/
theorem source_normalizer_eq_self (B5:Sylow 5 d.toTypeRuSetup.H) (F:Subgroup G)
    (h5:Q₅ d B5≤F) (e:F≃*ReeF4.Model 0) : normalizer (F:Set G)=F := by
  have hZ:d.toTypeRuSetup.Z≤F:=
    d.Z_le_V.trans ((le_conjugateSpan _ _).trans ((U_le_Q₅ d B5).trans h5))
  have hC:centralizer (F:Set G)≤F:=
    ((centralizer_le h5).trans_eq (centralizer_Q₅ d B5)).trans hZ
  have hs:Function.Surjective (MulAut.conj:F→*MulAut F):=
    fun α=>Tits.ExceptionalParabolics.FullRee.inner_of_equiv e α
  have he:=normalizerMonoidHom_comap_conj_range F
  rw [MonoidHom.range_eq_top.mpr hs,comap_top,sup_eq_left.mpr hC] at he
  apply le_antisymm _ F.le_normalizer
  intro g hg
  have hm:(⟨g,hg⟩:normalizer (F:Set G))∈(⊤:Subgroup (normalizer (F:Set G))):=mem_top _
  rw [he] at hm
  exact hm

/-- J.5.3's orbit size with normalizer escape discharged by the actual Q₅. -/
theorem source_first_orbit (B5:Sylow 5 d.toTypeRuSetup.H) {F M:Subgroup G}
    (h5:Q₅ d B5≤F) (e:F≃*ReeF4.Model 0) (hM:M⋖F) (hc:Nat.card M=20480)
    {g:G} (hgM:g∈normalizer (M:Set G)) (hgF:g∉F) :
    stabilizer F (g•basePoint F)=M.subgroupOf F ∧
      Nat.card (orbit F (g•basePoint F))=1755 := by
  have hn:g∉normalizer (F:Set G):=by rwa [source_normalizer_eq_self d B5 F h5 e]
  exact ⟨stabilizer_coset_eq_of_covBy hM hgM hn,source_first_orbit_card e hM hc hgM hn⟩

end CFSG.Quasithin.ChapterJ.Section05
