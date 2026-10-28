module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.RootGeneration
/-!
# Recovering the ambient group from its original cubic graph

The root subgroups generate G and are intrinsic pointwise neighborhood
stabilizers. Transporting the faithful action across any graph isomorphism
therefore lands in the second ambient group. Equal original group orders
make the resulting injection an isomorphism, equivariant with the graph
map. Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem points_generate : sSup c.points=⊤ := by
  let R := sSup c.points
  have hn : normalizer (R:Set G)=⊤ := by
    apply top_unique
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hh : R.conjBy g≤R := by
      apply map_le_iff_le_comap.mpr
      exact sSup_le (fun U hU=>map_le_iff_le_comap.mp (le_sSup (c.point_conjugate_mem hU g)))
    exact hh (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  let : R.Normal := normalizer_eq_top_iff.mp hn
  exact c.normal_eq_top_of_root_le R (le_sSup c.point_mem)

omit [Finite G] in
theorem root_fixes_neighbor_at (U : c.points) {u : G} (hu : u∈U.val) (V : c.points)
    (hUV : c.collinearity.Adj U V) : c.graphAction u V=V := by
  exact Subtype.ext (mem_normalizer_iff_map_conj_eq.mp ((c.neighbor_centralizes hUV).trans
    (Subgroup.centralizer_le_normalizer _) hu))

theorem graph_aut_mem_range_of_fixes_neighborhood (f : c.collinearity ≃g c.collinearity)
    (U : c.points) (hfU : f U=U)
    (hperp : ∀V:c.points,c.collinearity.Adj U V→f V=V) : f∈c.graphAction.range := by
  obtain ⟨g,hg⟩ := U.property
  let a := c.graphAction g
  let Wp : c.points := ⟨c.W,c.point_mem⟩
  have ha : a Wp=U := Subtype.ext hg.symm
  let f' := a.trans (f.trans a.symm)
  have hbase' : f' Wp=Wp := by
    change a.symm (f (a Wp))=Wp
    rw [ha,hfU,←ha,a.symm_apply_apply]
  have hperp' (V:c.points) (hV:c.collinearity.Adj Wp V) : f' V=V := by
    have hh : c.collinearity.Adj U (a V) := ha ▸ a.map_rel_iff.mpr hV
    change a.symm (f (a V))=V
    rw [hperp _ hh,a.symm_apply_apply]
  obtain ⟨w,-,he⟩ := (c.graph_aut_fixes_closed_neighborhood_iff f').mp ⟨hbase',hperp'⟩
  refine ⟨g*w*g⁻¹,?_⟩
  apply RelIso.ext
  intro V
  have hh := congrArg a (DFunLike.congr_fun he (a.symm V))
  change a (a.symm (f (a (a.symm V))))=a (c.graphAction w (a.symm V)) at hh
  rw [a.apply_symm_apply,a.apply_symm_apply] at hh
  rw [map_mul,map_mul,map_inv]
  exact hh.symm

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
variable {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

@[expose] noncomputable def transportGraphAction (F : c.collinearity ≃g c'.collinearity) :
    G→*(c'.collinearity ≃g c'.collinearity) where
  toFun g := F.symm.trans ((c.graphAction g).trans F)
  map_one' := by
    apply RelIso.ext
    intro U
    change F (c.graphAction 1 (F.symm U))=U
    rw [map_one]
    exact F.apply_symm_apply U
  map_mul' g k := by
    apply RelIso.ext
    intro U
    change F (c.graphAction (g*k) (F.symm U))=
      F (c.graphAction g (F.symm (F (c.graphAction k (F.symm U)))))
    rw [map_mul,F.symm_apply_apply]
    rfl

theorem transportGraphAction_range_le (F : c.collinearity ≃g c'.collinearity) :
    (c.transportGraphAction c' F).range≤c'.graphAction.range := by
  let N := c'.graphAction.range.comap (c.transportGraphAction c' F)
  have hN : N=⊤ := by
    apply top_unique
    rw [←c.points_generate]
    apply sSup_le
    intro U hU u hu
    let Up : c.points := ⟨U,hU⟩
    apply c'.graph_aut_mem_range_of_fixes_neighborhood _ (F Up)
    · change F (c.graphAction u (F.symm (F Up)))=F Up
      rw [F.symm_apply_apply]
      exact congrArg F (Subtype.ext (mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer hu)))
    · intro V hV
      have ha : c.collinearity.Adj Up (F.symm V) := by
        apply F.map_rel_iff.mp
        simpa only [F.apply_symm_apply] using hV
      change F (c.graphAction u (F.symm V))=V
      rw [c.root_fixes_neighbor_at Up hu _ ha,F.apply_symm_apply]
  rintro _ ⟨g,rfl⟩
  exact (show g∈N from hN.symm ▸ mem_top g)

theorem group_equiv_of_graph_iso (F : c.collinearity ≃g c'.collinearity) :
    ∃e:G≃*G',∀g:G,∀U:c.points,F (c.graphAction g U)=c'.graphAction (e g) (F U) := by
  let f : G→*c'.graphAction.range := (c.transportGraphAction c' F).codRestrict _
    (fun g=>c.transportGraphAction_range_le c' F ⟨g,rfl⟩)
  let E := MonoidHom.ofInjective c'.graphAction_injective
  let q : G→*G' := E.symm.toMonoidHom.comp f
  have he (g:G) : c'.graphAction (q g)=c.transportGraphAction c' F g :=
    congrArg Subtype.val (E.apply_symm_apply (f g))
  have hi : Function.Injective q := by
    intro g k hgk
    have hh : c.transportGraphAction c' F g=c.transportGraphAction c' F k :=
      (he g).symm.trans ((congrArg c'.graphAction hgk).trans (he k))
    apply c.graphAction_injective
    apply RelIso.ext
    intro U
    have hu := DFunLike.congr_fun hh (F U)
    change F (c.graphAction g (F.symm (F U)))=F (c.graphAction k (F.symm (F U))) at hu
    rw [F.symm_apply_apply] at hu
    exact F.injective hu
  have hc : Nat.card G'≤Nat.card G := by rw [c.ambient_card,c'.ambient_card]
  let e : G≃*G' := MulEquiv.ofBijective q (hi.bijective_of_nat_card_le hc)
  refine ⟨e,?_⟩
  intro g U
  have hh := DFunLike.congr_fun (he g) (F U)
  change c'.graphAction (e g) (F U)=F (c.graphAction g (F.symm (F U))) at hh
  rw [F.symm_apply_apply] at hh
  exact hh.symm
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

