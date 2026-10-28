module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Action
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The source plane actor for the ordinary A₆ quotient

The literal quotient L/O₂(L) ≃ A₆ identifies the kernel of the marked
six-point action. Transporting the syntheme quotient gives the cubic plane
action and its two-group kernel. The existing source plane-core theorem
then gives [V,X]=V, V ≤ O₂(X), and nonabelian O₂(X), for the actual
X=O²(L∩N_G(V₂)). Original 13.3.14 noncentrality makes X normal in N_G(V₂),
so the closure of the plane-normalizer conjugates of V lies in O₂(X) ≤ L.

This ordinary quotient specialization is consumed by OrdinaryLifting in
the original F.9(e) branch. Its earlier plane-noncentrality premise is
retained explicitly for the source assembler.
Source: Aschbacher--Smith, 13.5.4 and 13.5.6, printed pp.916--917.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Ordinary
open Section08.SourceCompletion Section07.NaturalAction AmbientSource
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem local_kernel_eq_core (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (localMap d).ker = pCore 2 L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), card_bot]
  have hc : Section08.TransvectionRecognition.Component.ModelExtension.centralCore L = pCore 2 L := by
    change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  rw [← hc]
  ext l
  change ((d.local_quotient (QuotientGroup.mk' _ l)) : Equiv.Perm (Fin 6)) = 1 ↔ _
  constructor
  · intro hh
    have hh' : d.local_quotient (QuotientGroup.mk' _ l) = 1 := Subtype.ext hh
    exact (QuotientGroup.eq_one_iff l).mp (d.local_quotient.injective (hh'.trans (map_one _).symm))
  · intro hl
    have hh : QuotientGroup.mk' _ l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [hh,map_one]
    rfl

private theorem localMap_fixes_iff (l:L) (W:Subgroup G)(hWV:W≤V) :
    (∀w∈image d W,naturalRepresentation (Fin 6) (localMap d l) w=w) ↔
      l.val∈centralizer (W:Set G) := by
  constructor
  · intro hf
    apply mem_centralizer_iff.mpr
    intro w hw
    let wV:V:=⟨w,hWV hw⟩
    have he:=d.conjugation l wV
    have hfix:=hf (d.coordinate wV).toAdd ((mem_image d W _).mpr ⟨wV,hw,rfl⟩)
    have hh:=congrArg Subtype.val (d.coordinate.injective (he.trans hfix))
    change l.val*w*l.val⁻¹=w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hc w hw
    obtain ⟨v,hv,rfl⟩:=(mem_image d W w).mp hw
    have hh:=mem_centralizer_iff.mp hc v.val hv
    have he:V.normalizerMonoidHom ⟨l.val,d.normalizes_V (mem_sup_left l.property)⟩ v=v:=by
      apply Subtype.ext
      change l.val*v.val*l.val⁻¹=v.val
      rw [←hh,mul_inv_cancel_right]
    exact (d.conjugation l v).symm.trans (congrArg (fun v:V=>(d.coordinate v).toAdd) he)

omit d in
private theorem conjugate_fixes (a g:Equiv.Perm (Fin 6)) :
    (∀v∈canonicalPlane,naturalRepresentation (Fin 6) (a⁻¹*g*a) v=v) ↔
      (∀v∈move a canonicalPlane,naturalRepresentation (Fin 6) g v=v) := by
  let ρ:=naturalRepresentation (Fin 6)
  constructor
  · intro h v hv
    obtain ⟨w,hw,rfl⟩:=hv
    have hh:=congrArg (ρ a) (h w hw)
    simpa only [map_mul,Module.End.mul_apply,ρ,(naturalRepresentation (Fin 6)).self_inv_apply] using hh
  · intro h v hv
    have hh:=congrArg (ρ a⁻¹) (h (ρ a v) (Submodule.mem_map_of_mem hv))
    simpa only [map_mul,Module.End.mul_apply,ρ,(naturalRepresentation (Fin 6)).inv_self_apply] using hh

theorem exists_planeLocal_quotient (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6)) :
    ∃q:planeLocal (L:=L) (V₂:=V₂)→*Equiv.Perm (Fin 3),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∀g,q g=1 ↔ g.val∈centralizer (V₂:Set G) := by
  obtain ⟨a,_,ha⟩:=QuadraticSource.source_even_flag d
  let f:=planeLocalMap d
  let c:Equiv.Perm (Fin 6)→*Equiv.Perm (Fin 6):=(MulAut.conj a.val⁻¹).toMonoidHom
  have hf:f.range=L2.map (MulAut.conj a.val).toMonoidHom:=by
    rw [planeLocalMap_range d,planeLocal_image d,ha,flagStabilizer_move,flagStabilizer_plane,
      L2,Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,conjugate_alternating]
  have hcf:(c.comp f).range=L2:=by
    rw [MonoidHom.range_comp,hf,map_map]
    have he:c.comp (MulAut.conj a.val).toMonoidHom=MonoidHom.id _:=by
      apply MonoidHom.ext
      intro x
      change a.val⁻¹*(a.val*x*a.val⁻¹)*(a.val⁻¹)⁻¹=x
      group
    rw [he,Subgroup.map_id]
  let α:planeLocal (L:=L) (V₂:=V₂)→*a6SynthemeStabilizer:={
    toFun:=fun g=>⟨⟨c (f g), (hcf ▸ (show c (f g)∈(c.comp f).range from ⟨g,rfl⟩)).2⟩,
      (hcf ▸ (show c (f g)∈(c.comp f).range from ⟨g,rfl⟩)).1⟩
    map_one':=by apply Subtype.ext; apply Subtype.ext; exact map_one (c.comp f)
    map_mul':=by intros; apply Subtype.ext; apply Subtype.ext; exact map_mul (c.comp f) _ _ }
  have hα:Function.Surjective α:=by
    intro y
    have hy:y.val.val∈(c.comp f).range:=hcf ▸ (show y.val.val∈L2 from ⟨y.property,y.val.property⟩)
    obtain ⟨g,hg⟩:=hy
    exact ⟨g,Subtype.ext (Subtype.ext hg)⟩
  have hkα:IsPGroup 2 α.ker:=by
    apply ((show IsPGroup 2 (localMap d).ker by rw [local_kernel_eq_core d e]; exact pCore_isPGroup).comap_of_injective (inclusion (show planeLocal (L:=L) (V₂:=V₂)≤L from inf_le_left))
      (inclusion_injective _)).to_le
    intro g hg
    have hh: c (f g)=1:=congrArg (fun y:a6SynthemeStabilizer=>y.val.val) hg
    have hh': f g=1 := (MulAut.conj a.val⁻¹).injective (hh.trans (map_one c).symm)
    exact hh'
  let q:=a6SynthemeQuotientHom.comp α
  refine ⟨q,a6SynthemeQuotientHom_surjective.comp hα,?_,?_⟩
  · have hk:IsPGroup 2 a6SynthemeQuotientHom.ker:=by rw [a6SynthemeQuotientHom_ker]; exact pCore_isPGroup
    exact hk.comap_of_ker_isPGroup α hkα
  · intro g
    change a6SynthemeQuotientHom (α g)=1 ↔ _
    rw [PlaneAction.even_syntheme_quotient_eq_one_iff]
    change (∀v∈canonicalPlane,naturalRepresentation (Fin 6) (a.val⁻¹*f g*a.val) v=v) ↔ _
    rw [conjugate_fixes,←ha]
    exact localMap_fixes_iff d (inclusion (show planeLocal (L:=L) (V₂:=V₂)≤L from inf_le_left) g)
      V₂ (d.plane_le_seed.trans d.seed_le)

theorem planeActor_action_source (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6)) :
    (letI := source_plane_isKleinFour d;
      Nat.card (((planeActor (L:=L) (V₂:=V₂)).subgroupOf (normalizer (V₂:Set G))).map
        (planeAction V₂))=3) ∧
    IsPGroup 2 (planeActor (L:=L) (V₂:=V₂) ⊓ centralizer (V₂:Set G):Subgroup G) := by
  let := source_plane_isKleinFour d
  let P:=planeLocal (L:=L) (V₂:=V₂)
  let X:=planeActor (L:=L) (V₂:=V₂)
  let N:=normalizer (V₂:Set G)
  let r:P→*Equiv.Perm (Fin 3):=(planeAction V₂).comp (inclusion (show P≤N from inf_le_right))
  obtain ⟨q,hq,hk,hfix⟩:=exists_planeLocal_quotient d e
  have heker:r.ker=q.ker:=by
    ext g
    exact (planeAction_eq_one V₂ (inclusion (show P≤N from inf_le_right) g)).trans (hfix g).symm
  have hr:Function.Surjective r:=by
    apply MonoidHom.range_eq_top.mp
    apply r.range.eq_top_of_card_eq
    rw [←index_ker,heker,index_ker,MonoidHom.range_eq_top.mpr hq,card_top]
  have hmap:(X.subgroupOf N).map (planeAction V₂)=(pResidual 2 P).map r:=by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨p,hp,he⟩:=hx
      refine ⟨p,hp,?_⟩
      exact congrArg (planeAction V₂) (Subtype.ext he)
    · rintro ⟨p,hp,rfl⟩
      exact ⟨inclusion (show P≤N from inf_le_right) p,⟨p,hp,rfl⟩,rfl⟩
  constructor
  · change Nat.card ((X.subgroupOf N).map (planeAction V₂))=3
    rw [hmap,map_pResidual_of_surjective 2 r hr,Equiv.Perm.twoResidual_eq_alternating,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · have hkimage:q.ker.map P.subtype=P⊓centralizer (V₂:Set G):=by
      ext g
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p.property,(hfix p).mp hp⟩
      · intro hg
        exact ⟨⟨g,hg.1⟩,(hfix _).mpr hg.2,rfl⟩
    apply ((hk.map P.subtype).of_equiv (MulEquiv.subgroupCongr hkimage)).to_le
    exact inf_le_inf_right _ planeActor_le

/-- The plane kernel is the intrinsic two-core, and the quotient is cubic. -/
theorem planeActor_core_source (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6)) :
    (planeActor (L:=L) (V₂:=V₂)).pCoreIn 2=
      planeActor (L:=L) (V₂:=V₂)⊓centralizer (V₂:Set G) ∧
      Nat.card (planeActor (L:=L) (V₂:=V₂) ⧸ pCore 2 (planeActor (L:=L) (V₂:=V₂)))=3 := by
  let := source_plane_isKleinFour d
  let X:=planeActor (L:=L) (V₂:=V₂)
  have hn:X≤normalizer (V₂:Set G):=planeActor_le.trans inf_le_right
  let f:X→*Equiv.Perm (Fin 3):=(planeAction V₂).comp (inclusion hn)
  obtain ⟨hc,hk⟩:=planeActor_action_source d e
  have hf:f.range=(X.subgroupOf (normalizer (V₂:Set G))).map (planeAction V₂):=by
    ext g
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨inclusion hn x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
  have hc':Nat.card f.range=3:=by rw [hf]; exact hc
  have hker:f.ker=(centralizer (V₂:Set G)).subgroupOf X:=by
    ext x
    exact planeAction_eq_one V₂ (inclusion hn x)
  have hkp:IsPGroup 2 f.ker:=by
    apply hk.comap_subtype.to_le
    intro x hx
    have hc:x∈(centralizer (V₂:Set G)).subgroupOf X:=hker ▸ hx
    exact ⟨x.property,hc⟩
  have hcore:pCore 2 f.range=⊥:=by
    apply card_eq_one.mp
    rcases (pCore_isPGroup (p:=2) (G:=f.range)).card_eq_or_dvd with hh|hh
    · exact hh
    · have hd:=hh.trans (card_subgroup_dvd_card (pCore 2 f.range))
      rw [hc'] at hd
      norm_num at hd
  have he:=f.ker_eq_pCore_of_range_core_eq_bot 2 hkp hcore
  constructor
  · change (pCore 2 X).map X.subtype=_
    rw [←he,hker,subgroupOf_map_subtype,inf_comm]
  · change Nat.card (X⧸pCore 2 X)=3
    rw [←he,Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hc']

/-- The literal original residual, without a separate plane actor,
cubic-image, kernel or module-generation premise. -/
theorem source_planeActor_nonabelian_core (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6)) :
    ⁅V,planeActor (L:=L) (V₂:=V₂)⁆=V ∧
      V≤(planeActor (L:=L) (V₂:=V₂)).pCoreIn 2 ∧
      ¬IsMulCommutative (pCore 2 (planeActor (L:=L) (V₂:=V₂))) := by
  obtain ⟨hx,hk⟩:=planeActor_action_source d e
  have hXL:planeActor (L:=L) (V₂:=V₂)≤L:=planeActor_le.trans inf_le_left
  have hXN:planeActor (L:=L) (V₂:=V₂)≤normalizer (V₂:Set G):=planeActor_le.trans inf_le_right
  have hh:=source_plane_residual_core_nonabelian d _ hXL hXN (planeActor_normalized d)
    planeActor_twoPerfect hx hk
  exact ⟨hh.1,hh.2.1,source_plane_intrinsic_core_nonabelian d _ hXL hXN
    (planeActor_normalized d) planeActor_twoPerfect hx hk⟩

/-- The original noncentrality theorem13.3.14 now suffices to normalize
this same residual by the full ambient plane normalizer. -/
theorem source_planeActor_normalized
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    normalizer (V₂:Set G)≤normalizer (planeActor (L:=L) (V₂:=V₂):Set G) := by
  let := source_plane_isKleinFour d
  obtain ⟨hx,hk⟩:=planeActor_action_source d e
  exact (plane_normalClosure T V₁ V₂ (planeActor (L:=L) (V₂:=V₂)) d.line_card d.line_le_plane
    d.line_stable d.plane_stable (planeActor_le.trans inf_le_right)
    (planeActor_normalized d) planeActor_twoPerfect hx hk hm).2.1


theorem source_plane_closure_le_actor_core
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    conjugateSpanBy V (normalizer (V₂:Set G))≤
      (planeActor (L:=L) (V₂:=V₂)).pCoreIn 2 := by
  exact conjugateSpanBy_le (source_planeActor_nonabelian_core d e).2.1
    ((source_planeActor_normalized d e hm).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

theorem source_plane_closure_generated
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    ⁅conjugateSpanBy V (normalizer (V₂:Set G)),planeActor (L:=L) (V₂:=V₂)⁆=
      conjugateSpanBy V (normalizer (V₂:Set G)) := by
  exact commutator_conjugateSpanBy_eq_self _ _ _ (planeActor_le.trans inf_le_right)
    (source_planeActor_normalized d e hm) (source_planeActor_nonabelian_core d e).1

theorem source_plane_conjugate_le_local
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥)
    (g:G) (hg:g∈normalizer (V₂:Set G)) :
    V.map (MulAut.conj g).toMonoidHom≤QuadraticSource.localModuleNormalizer (M:=M) (V:=V) := by
  have hv:V.map (MulAut.conj g).toMonoidHom≤conjugateSpanBy V (normalizer (V₂:Set G)):=by
    rintro _ ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V _ hg) v).mp
      (le_conjugateSpanBy _ _ hv)
  exact hv.trans ((source_plane_closure_le_actor_core d e hm).trans
    ((pCoreIn_le 2 _).trans ((planeActor_le.trans inf_le_left).trans (QuadraticSource.L_le_local d))))

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Ordinary
