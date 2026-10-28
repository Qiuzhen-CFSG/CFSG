module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointResidualRestriction.TwoKernel
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.F9Placement
public import CFSG.Quasithin.ChapterF.Section09.F7Specialization

/-!
# The ordinary13.3.9 residual conclusion in the original F.9 setup

The literal point centralizer in L has Sylow index three: its natural image
has that index and its kernel is the two-core. The preceding theta and
core-free-join argument places Y inside L. Since F.9 puts C_L(V₁) inside H,
relative normality of Y in H makes Y Sylow-normalized in this point group.
The index-three residual argument therefore gives Y=1 or Y=L₁, where L₁
is exactly the original embedded O²(C_L(V₁)).

The theorem chooses the unique nonidentity point of V₁ and supplies every
local prime-divisor, Sylow, and point-normalizer consequence internally.
The natural marking and the genuine earlier theta/normalization inputs remain
explicit for the source assembly.
Source: Aschbacher–Smith13.3.9, p.887, applied in13.7.4(1), pp.936–938.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.PointResidualImage
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


theorem ordinary_point_sylow_index_three {G:Type*} [Group G] [Finite G]
    (L V:Subgroup G) [IsElementaryAbelian 2 V] (hLV:L≤normalizer (V:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation L V hLV l v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (w:Additive V) (hw:w≠0)
    (T:Sylow 2 (L⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G)) :
    (T:Subgroup (L⊓centralizer ({(w.toMul:G)}:Set G) : Subgroup G)).index=3 := by
  let J:=L⊓centralizer ({(w.toMul:G)}:Set G)
  let q:J→*S:=(alternatingGroup (Fin 6)).subtype.comp (α.comp (inclusion inf_le_left))
  let line:=Submodule.span (ZMod 2) {e w}
  have hew:e w≠0 := by
    intro hh
    exact hw (e.injective (hh.trans e.map_zero.symm))
  have hdim:Module.finrank (ZMod 2) line=1:=finrank_span_singleton hew
  have hfix (l:L): (α l:S)∈subspaceStabilizer (naturalRepresentation (Fin 6)) line ↔
      (l:G)∈centralizer ({(w.toMul:G)}:Set G) := by
    rw [binary_line_mem _ _ hew]
    change alternatingNaturalRepresentation (Fin 6) (α l) (e w)=e w ↔ _
    rw [←he,e.injective.eq_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have hc:=congrArg (fun v:Additive V=>(v.toMul:G)) hh
      exact mul_inv_eq_iff_eq_mul.mp hc
    · intro hh
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l:G)*(w.toMul:G)*(l:G)⁻¹=(w.toMul:G)
      rw [hh,mul_inv_cancel_right]
  have hr:q.range=alternatingGroup (Fin 6)⊓subspaceStabilizer (naturalRepresentation (Fin 6)) line := by
    apply le_antisymm
    · rintro _ ⟨j,rfl⟩
      exact ⟨(α (inclusion inf_le_left j)).property,(hfix _).mpr j.property.2⟩
    · rintro x ⟨hx,hfixx⟩
      obtain ⟨l,hl⟩:=hα ⟨x,hx⟩
      have hlf:(l:G)∈centralizer ({(w.toMul:G)}:Set G) := (hfix l).mp (by rw [hl];exact hfixx)
      exact ⟨⟨l,⟨l.property,hlf⟩⟩,congrArg Subtype.val hl⟩
  have hk:IsPGroup 2 q.ker := by
    let i:q.ker→*pCore 2 L :=
      ((inclusion (show J≤L from inf_le_left)).comp q.ker.subtype).codRestrict _ (fun x=>by
        rw [←action_kernel_eq_core L α hα eL]
        apply Subtype.ext
        exact x.property)
    apply (pCore_isPGroup (p:=2) (G:=L)).of_injective i
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z:pCore 2 L=>(z.val:G)) hh
  exact point_hom_sylow_index_three q (alternatingGroup (Fin 6)) le_rfl line hdim hr hk T
variable {G:Type*} [Group G] [Finite G]

theorem ordinary_residual_of_f9_theta (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (M Y:Subgroup G) [IsElementaryAbelian 2 D.V]
    (hLP:D.L≤M⊓normalizer (D.V:Set G))
    (hPL:M⊓normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (α:D.L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (eL:(D.L⧸pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (e:Additive D.V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:D.L) (v:Additive D.V), e (conjugationRepresentation
      (M⊓normalizer (D.V:Set G)) D.V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (htheta:closure {x:G|x∈M ∧ orderOf x=3}=D.L) (hp:IsPPerfect 2 Y)
    (hY:Y≤M⊓normalizer (D.V:Set G)) (hYH:Y≤D.H)
    (hnY:D.H≤normalizer (Y:Set G))
    : Y=⊥ ∨ Y=D.L₁ := by
  obtain ⟨v,hv,hunique⟩ := (Nat.card_eq_two_iff' (1:D.V₁)).mp h.point_card
  have hvV:(v:G)∈D.V := (h.point_lt.le.trans h.plus_le) v.property
  let w:Additive D.V:=Additive.ofMul ⟨v,hvV⟩
  have hw:w≠0 := by
    intro hh
    apply hv
    apply Subtype.ext
    exact congrArg (fun x:Additive D.V=>(x.toMul:G)) hh
  have hC:centralizer ({(w.toMul:G)}:Set G)=D.Gz := by
    apply le_antisymm
    · intro x hx y hy
      by_cases hy1:y=1
      · simp [hy1]
      have hyv:(⟨y,hy⟩:D.V₁)=v := hunique _ (fun he=>hy1 (congrArg Subtype.val he))
      have hyv':y=(w.toMul:G):=congrArg Subtype.val hyv
      rw [hyv']
      exact (mem_centralizer_singleton_iff.mp hx).symm
    · exact centralizer_le (Set.singleton_subset_iff.mpr v.property)
  have hc:Y≤centralizer ({(w.toMul:G)}:Set G) := hC.symm ▸ hYH.trans h.H_centralizes
  have hYL:=le_component_of_f9_theta D h M Y hLP hPL α hα eL e he htheta hp
    hY hYH hnY w hw hc
  let J:=D.L⊓D.Gz
  have hYJ:Y≤J:=le_inf hYL (hYH.trans h.H_centralizes)
  have hJH:J≤D.H := by
    have hh:J≤D.LT⊓normalizer (D.V₁:Set G) :=
      le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    rw [h.normalizer_point_LT_eq] at hh
    exact hh.trans h.local_le
  let T:Sylow 2 J:=Classical.choice inferInstance
  have hi:(T:Subgroup J).index=3 := by
    have hh:=ordinary_point_sylow_index_three D.L D.V (hLP.trans inf_le_right)
      α hα eL e (fun l u=>he l u) w hw
    rw [hC] at hh
    exact hh T
  have hp':IsPPerfect 2 (Y.subgroupOf J) := hp.of_surjective
    (subgroupOfEquivOfLe hYJ).symm.toMonoidHom (subgroupOfEquivOfLe hYJ).symm.surjective
  have hn:(T:Subgroup J)≤normalizer (Y.subgroupOf J:Set J) := by
    intro t _
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hnY (hJH t.property)) y.val
  rcases eq_bot_or_residual_of_index_three (T:Subgroup J) (Y.subgroupOf J)
    T.isPGroup' hi hp' hn with hb|hb
  · left
    have hh:=congrArg (Subgroup.map J.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hYJ,Subgroup.map_bot] using hh
  · right
    change Y=(pResidual 2 J).map J.subtype
    have hh:=congrArg (Subgroup.map J.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hYJ] using hh
end CFSG.Quasithin.Chapter13.Section03.PointResidualImage
