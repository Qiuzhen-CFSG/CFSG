module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.MarkedCore
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Axes
public import Theory.GroupTheory.DihedralSymmetricFour.FactorSylow
/-!
# The original Sylow placement and ordered factor axes

The dihedral factor is normal in the literal centralizer and hence lies
in the original Sylow J(T). Intersecting the symmetric factor with that
Sylow gives its dihedral Sylow. Its central involution lies in the original
four-group {1,t,z,tz}; disjointness excludes t and source nonfusion excludes
z, leaving tz. The Klein four-group stays inside B and J(T).
Source: Aschbacher–Smith 13.9.10, printed p.973.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The native split has both dihedral factors in the original J(T), with its original ordered axes. -/
theorem exists_source_aligned_split {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃(f g:D8→*G) (X:Subgroup G) (_eX:X≃*S4)
      (split:normalizerCentralizer m.B m.t≃*f.range×X),
      Function.Injective f ∧ f.range≤m.dihedralBase ∧ g.range≤m.dihedralBase ∧
      f (.r 2)=m.t ∧ g (.r 2)=m.t*m.z ∧
      (∀a b,Commute (f a) (g b)) ∧ Disjoint f.range X ∧
      f.range≤centralizer (X:Set G) ∧ X≤normalizer (m.B:Set G) ∧
      X.pCoreIn 2≤m.B ∧ X.pCoreIn 2≤m.dihedralBase ∧ m.t*m.z∈X.pCoreIn 2 ∧
      (∀x∈X.pCoreIn 2,x≠1→IsConj m.t x) ∧
      (∀c:normalizerCentralizer m.B m.t,(c:G)=((split c).1:G)*((split c).2:G)) := by
  obtain ⟨R,X,split,eR,eX,hcoord,hRC,hXC,hcomm,hdisj,hft,hVB,hfusion⟩:=
    m.exists_marked_centralizer_split_with_core hG
  let C := normalizerCentralizer m.B m.t
  have hJC : m.dihedralBase≤C := by
    refine le_inf (m.dihedralBase_le_sylow.trans m.sylow_le_normalizer_B) ?_
    rw [←m.elementary_thompson,←m.sylow_centralizer_t]
    exact inf_le_right
  have hcJ : Nat.card m.dihedralBase=64 := by
    rw [dihedralBase,m.card_image,card_J]
  have hcC : Nat.card C=192 := by
    rw [Nat.card_congr split.toEquiv,Nat.card_prod,
      ←Nat.card_congr eR.toEquiv,←Nat.card_congr eX.toEquiv]
    norm_num [DihedralGroup.card,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  let S:Sylow 2 C := Sylow.ofCard (m.dihedralBase.subgroupOf C) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv,hcJ,hcC]
    decide +kernel)
  have hSJ : (S:Subgroup C).map C.subtype=m.dihedralBase :=
    map_subgroupOf_eq_of_le hJC
  have hRJ : R≤m.dihedralBase := hSJ ▸
    DihedralSymmetricFour.first_factor_le_sylow C R X hRC hXC split hcoord hcomm eR S
  obtain ⟨P,hP⟩:=DihedralSymmetricFour.second_factor_sylow C R X hRC hXC split hcoord hcomm S
  rw [hSJ] at hP
  obtain ⟨eP⟩:=DihedralSymmetricFour.sylow_dihedral eX.symm P
  let f:D8→*G := R.subtype.comp eR.toMonoidHom
  let gx:D8→*X := (P:Subgroup X).subtype.comp eP.toMonoidHom
  let g:D8→*G := X.subtype.comp gx
  have hf : Function.Injective f := Subtype.val_injective.comp eR.injective
  have hg : Function.Injective g := Subtype.val_injective.comp (Subtype.val_injective.comp eP.injective)
  have hfr : f.range=R := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact (eR a).property
    · intro hx
      obtain ⟨a,ha⟩:=eR.surjective ⟨x,hx⟩
      exact ⟨a,congrArg Subtype.val ha⟩
  have hgP (a:D8) : g a∈(P:Subgroup X).map X.subtype := ⟨gx a,(eP a).property,rfl⟩
  have hgJ : g.range≤m.dihedralBase := by
    rintro _ ⟨a,rfl⟩
    exact (hP ▸ hgP a).1
  have hgne : g (.r 2)≠1 := by
    intro he
    exact (by decide : (.r 2:D8)≠1) (hg (he.trans (map_one g).symm))
  have hcore : g (.r 2)∈X.pCoreIn 2 := by
    have hh:=dihedral_square_mem_symmetric_core (eX.symm.toMonoidHom.comp gx)
    have hx : gx (.r 2)∈pCore 2 X := by
      rw [←pCore_map_iso 2 eX]
      exact ⟨eX.symm (gx (.r 2)),hh,eX.apply_symm_apply _⟩
    exact ⟨gx (.r 2),hx,rfl⟩
  have hgt : g (.r 2)=m.t*m.z := by
    have hc : ∀y∈m.dihedralBase,y*g (.r 2)=g (.r 2)*y := by
      intro y hy
      exact DihedralSymmetricFour.second_sylow_center C R X hRC hXC split hcoord hcomm S
        (hSJ.symm ▸ hRJ) P (hSJ.symm ▸ hP) eP y (hSJ.symm ▸ hy)
    rcases m.central_dihedralBase_cases (g (.r 2)) (hgJ ⟨_,rfl⟩) hc with h|h|h|h
    · exact (hgne h).elim
    · have htR : m.t∈R := hft ▸ (eR (.r 2)).property
      have htX : m.t∈X := h ▸ (gx (.r 2)).property
      exact (m.t_ne_one (disjoint_def.mp hdisj htR htX)).elim
    · exact (m.not_isConj_t_z (h ▸ hfusion _ hcore hgne)).elim
    · exact h
  let split' : C≃*f.range×X := split.trans ((MulEquiv.subgroupCongr hfr.symm).prodCongr (MulEquiv.refl X))
  refine ⟨f,g,X,eX.symm,split',hf,hfr.symm ▸ hRJ,hgJ,hft,hgt,?_,hfr.symm ▸ hdisj,
    hfr.symm ▸ hcomm,hXC.trans inf_le_left,hVB,?_,hgt ▸ hcore,hfusion,?_⟩
  · intro a b
    exact (mem_centralizer_iff.mp (hcomm (eR a).property) _ (gx b).property).symm
  · exact (X.pCoreIn_le_sylow P).trans (hP ▸ inf_le_left)
  · intro c
    exact hcoord c

end CFSG.Quasithin.Chapter13.Section09.Marking
