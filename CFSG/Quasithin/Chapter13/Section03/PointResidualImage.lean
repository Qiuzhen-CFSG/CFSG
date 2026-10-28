module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointResidualRestriction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Inputs

/-!
# The original barred point-residual image in 13.3.9

The natural A₆ marking extends to every group normalizing L and V. On a
point centralizer its image is exactly the corresponding natural-line
stabilizer: over F₂ stabilizing a line fixes its nonzero vector. The native
index-three restriction therefore identifies each Sylow-normalized two-perfect
image with either the trivial group or the full point residual. Equal action
kernels carry this conclusion back to the literal conjugation map on V.

The last theorem uses precisely the `barImage` of the source interface.
It proves the finite image step, without asserting the earlier normalization
of V, the theta/TI theorems, or recovery of Y=L₁ in the ambient group.

Source: Aschbacher–Smith, 13.3.9, printed p.887; the original natural-module
marking and normalization of V are supplied by 13.3.2 and 12.2.6.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
open Chapter13.Section08.TransvectionQuotients.FiveSeed
open Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

private theorem binary_line_mem {H W:Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ:Representation (ZMod 2) H W) (w:W) (hw:w≠0) (g:H) :
    g∈subspaceStabilizer ρ (Submodule.span (ZMod 2) {w}) ↔ ρ g w=w := by
  have hinj:Function.Injective (ρ g) := by
    intro x y hh
    have he:=congrArg (ρ g⁻¹) hh
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using he
  constructor
  · intro hg
    obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp ((hg w).mpr (Submodule.mem_span_singleton_self w))
    have ha0:a≠0 := by
      intro hz
      have hz':ρ g w=ρ g 0 := by simpa [hz] using ha.symm
      exact hw (hinj hz')
    have ha1:a=1 := (by decide:∀a:ZMod 2,a≠0→a=1) a ha0
    simpa [ha1] using ha.symm
  · intro hg x
    constructor
    · rintro hx
      obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨a,hinj (by simpa [hg] using ha)⟩
    · rintro hx
      obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hx
      simpa only [map_smul,hg] using
        Submodule.smul_mem (Submodule.span (ZMod 2) {w}) a (Submodule.mem_span_singleton_self w)

private theorem image_eq_of_kernel {H A B:Type*} [Group H] [Group A] [Group B]
    (a:H→*A) (b:H→*B) (hk:a.ker=b.ker) (D E:Subgroup H)
    (he:D.map b=E.map b) : D.map a=E.map a := by
  have hh:=congrArg (Subgroup.comap b) he
  rw [comap_map_eq,comap_map_eq,←hk] at hh
  have hh':=congrArg (Subgroup.map a) hh
  have hb:a.ker.map a=⊥ := map_ker_self a
  simpa only [Subgroup.map_sup,hb,sup_bot_eq] using hh'

variable {G:Type*} [Group G] [Finite G]

/-- The actual natural action restricts a point centralizer to its full residual
image. The subgroup is only assumed two-perfect and Sylow-normalized. -/
theorem natural_point_conjugation_image (P L V:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤P) (hPL:P≤normalizer (L:Set G)) (hPV:P≤normalizer (V:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l : L) (v : Additive V), e (conjugationRepresentation P V hPV (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (w:Additive V) (hw:w≠0)
    (T:Sylow 2 (P⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G))
    (Y:Subgroup (P⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G))
    (hp:IsPPerfect 2 Y) (hn:(T:Subgroup (P⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G))≤normalizer (Y:Set _)) :
    let J:=P⊓centralizer ({(w.toMul:G)}:Set G)
    let a: J→*MulAut V := (conjugationAut P V hPV).comp (inclusion inf_le_left)
    Y.map a=⊥ ∨ Y.map a=(pResidual 2 J).map a := by
  obtain ⟨f,hfL,hact,hker⟩:=natural_extension P L V hLP hPL hPV α hα e he
  let J:=P⊓centralizer ({(w.toMul:G)}:Set G)
  let fJ:J→*Equiv.Perm (Fin 6):=f.comp (inclusion inf_le_left)
  let a:J→*MulAut V := (conjugationAut P V hPV).comp (inclusion inf_le_left)
  let line:=Submodule.span (ZMod 2) {e w}
  have hew:e w≠0 := by
    intro hh
    exact hw (e.injective (hh.trans e.map_zero.symm))
  have hdim:Module.finrank (ZMod 2) line=1:=finrank_span_singleton hew
  have hI:alternatingGroup (Fin 6)≤f.range := by
    intro x hx
    obtain ⟨l,hl⟩:=hα ⟨x,hx⟩
    exact ⟨inclusion hLP l,(hfL l).trans (congrArg Subtype.val hl)⟩
  have hfix (p:P): f p∈subspaceStabilizer (naturalRepresentation (Fin 6)) line ↔
      (p:G)∈centralizer ({(w.toMul:G)}:Set G) := by
    rw [binary_line_mem _ _ hew]
    rw [←hact, e.injective.eq_iff]
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have hc:=congrArg (fun v:Additive V=>(v.toMul:G)) hh
      change (p:G)*(w.toMul:G)*(p:G)⁻¹=(w.toMul:G) at hc
      exact mul_inv_eq_iff_eq_mul.mp hc
    · intro hh
      apply Additive.toMul.injective
      apply Subtype.ext
      change (p:G)*(w.toMul:G)*(p:G)⁻¹=(w.toMul:G)
      rw [hh,mul_inv_cancel_right]
  have hr:fJ.range=f.range⊓subspaceStabilizer (naturalRepresentation (Fin 6)) line := by
    apply le_antisymm
    · rintro _ ⟨j,rfl⟩
      exact ⟨⟨inclusion inf_le_left j,rfl⟩,(hfix _).mpr j.property.2⟩
    · rintro x ⟨⟨p,rfl⟩,hp⟩
      exact ⟨⟨p,⟨p.property,(hfix p).mp hp⟩⟩,rfl⟩
  have hak:a.ker=fJ.ker := by
    ext j
    rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
    change conjugationAut P V hPV (inclusion inf_le_left j)=1 ↔ f (inclusion inf_le_left j)=1
    change conjugationAut P V hPV (inclusion inf_le_left j)=1 ↔
      inclusion (show J≤P from inf_le_left) j∈f.ker
    rw [hker]
    change _ ↔ ∀v∈V,v*(j:G)=(j:G)*v
    constructor
    · intro hh v hv
      have hh':=congrArg (fun k:MulAut V=>(k ⟨v,hv⟩:G)) hh
      exact (mul_inv_eq_iff_eq_mul.mp hh').symm
    · intro hh
      ext v
      change (j:G)*(v:G)*(j:G)⁻¹=(v:G)
      rw [←hh v v.property,mul_inv_cancel_right]
  change Y.map a=⊥ ∨ Y.map a=(pResidual 2 J).map a
  rcases point_image_twoPerfect fJ f.range hI line hdim hr T Y hp hn with hb|hb
  · left
    have hh:=image_eq_of_kernel a fJ hak Y ⊥ (by simpa using hb)
    simpa using hh
  · exact Or.inr (image_eq_of_kernel a fJ hak Y (pResidual 2 J) hb)
/-- Literal barred-image version of the finite step in 13.3.9, with
`P=M∩N(V)` and the original point centralizer. -/
theorem barImage_point_residual (M L V:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (w:Additive V) (hw:w≠0)
    (T:Sylow 2 ((M⊓normalizer (V:Set G))⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G))
    (Y:Subgroup G)
    (hY:Y≤(M⊓normalizer (V:Set G))⊓centralizer ({(w.toMul:G)}:Set G))
    (hp:IsPPerfect 2 Y)
    (hn:(T:Subgroup ((M⊓normalizer (V:Set G))⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G)).map
      ((M⊓normalizer (V:Set G))⊓centralizer ({(w.toMul:G)}:Set G)).subtype≤normalizer (Y:Set G)) :
    let J:Subgroup G:=(M⊓normalizer (V:Set G))⊓centralizer ({(w.toMul:G)}:Set G)
    Chapter13.Section08.SolvableExclusion.Residual.barImage M V Y=⊥ ∨
      Chapter13.Section08.SolvableExclusion.Residual.barImage M V Y=
        Chapter13.Section08.SolvableExclusion.Residual.barImage M V ((pResidual 2 J).map J.subtype) := by
  let P:=M⊓normalizer (V:Set G)
  let J:=P⊓centralizer ({(w.toMul:G)}:Set G)
  let a:J→*MulAut V := (conjugationAut P V inf_le_right).comp (inclusion inf_le_left)
  have hYJ:Y≤J:=hY
  have hp':IsPPerfect 2 (Y.subgroupOf J) := hp.of_surjective
    (subgroupOfEquivOfLe hYJ).symm.toMonoidHom (subgroupOfEquivOfLe hYJ).symm.surjective
  have hn':(T:Subgroup J)≤normalizer (Y.subgroupOf J:Set J) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hn (mem_map_of_mem _ ht)) y.val
  have hm (D:Subgroup J):D.map a=
      Chapter13.Section08.SolvableExclusion.Residual.barImage M V (D.map J.subtype) := by
    apply le_antisymm
    · rintro _ ⟨d,hd,rfl⟩
      refine ⟨inclusion (show J≤P from inf_le_left) d,?_,?_⟩
      · exact mem_map_of_mem J.subtype hd
      · rfl
    · rintro _ ⟨p,hp,rfl⟩
      obtain ⟨d,hd,heq⟩:=hp
      refine ⟨d,hd,?_⟩
      have hdp:inclusion (show J≤P from inf_le_left) d=p := Subtype.ext heq
      subst p
      rfl
  have hh:=natural_point_conjugation_image P L V hLP hPL inf_le_right α hα e he
    w hw T (Y.subgroupOf J) hp' hn'
  change (Y.subgroupOf J).map a=⊥ ∨ (Y.subgroupOf J).map a=(pResidual 2 J).map a at hh
  rw [hm,hm,map_subgroupOf_eq_of_le hYJ] at hh
  exact hh
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
