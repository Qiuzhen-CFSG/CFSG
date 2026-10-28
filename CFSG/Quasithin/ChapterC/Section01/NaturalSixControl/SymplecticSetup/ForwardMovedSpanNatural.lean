module
public import Theory.GroupTheory.Commutator.CentralFixedMoved
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanNatural
/-!
# The intrinsic natural central quotient of the moved terminal span

Write P for the forward normal span and P0=[P,L_alpha]. The literal map
P0 to P/Z(P) has image equal to the alternating moved space. Because
L_alpha fixes P', the three-subgroups lemma identifies the preimage of that
space's fixed vectors with Z(P0). The supplied natural moved-section
coordinates therefore descend to an isomorphism P0/Z(P0) with the natural
binary four-space, preserving the same symmetric-six marking and the actual
conjugation action of the original local group.

The proved terminal natural-section producer supplies those coordinates
without an extra recognition premise. In particular the intrinsic central
quotient has order sixteen; P0 is nonabelian, so its derived subgroup equals
the already established derived subgroup of P of order two. The source-data
and original Chapter13 consumers retain the literal characteristic reduction.

Source: MS93 (3.10), printed p.880, and the terminal paragraph of (5.12),
printed p.927.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterB.QuasisimpleSource



namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] (R : Subgroup M)
/-- The literal component-moved subgroup of the forward normal span. -/
@[expose] def forwardMovedSpan (c : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅localZSpan R c (alpha R),Ltilde R (alpha R)⁆
theorem forwardMovedSpan_le (c : Vertex R) :
    forwardMovedSpan R c≤localZSpan R c (alpha R) :=
  le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer _).trans (localZSpan_normalized R _ _))
theorem forwardMovedSpan_normalized (c : Vertex R) :
    stabilizer R (alpha R)≤normalizer (forwardMovedSpan R c:Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅localZSpan R c (alpha R),Ltilde R (alpha R)⁆).map (MulAut.conj g).toMonoidHom=_
  have hP : (localZSpan R c (alpha R)).map (MulAut.conj g).toMonoidHom=localZSpan R c (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized R c (alpha R) hg)
  rw [map_commutator,hP]
  have hL := Ltilde_act R g⁻¹ (alpha R)
  have hg' : act R g⁻¹ (alpha R)=alpha R := (stabilizer R (alpha R)).inv_mem hg
  simpa only [forwardMovedSpan,hg',inv_inv] using congrArg (fun D => ⁅localZSpan R c (alpha R),D⁆) hL.symm
/-- Original-group conjugation on the moved forward span. -/
@[expose] noncomputable def forwardMovedSpanAction (c : Vertex R) : M→*MulAut (forwardMovedSpan R c) :=
  (forwardMovedSpan R c).normalizerMonoidHom.comp ((embedM R).codRestrict _ (by
    intro m
    apply forwardMovedSpan_normalized R c
    change embedM R m∈stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩))
/-- Inclusion followed by the literal central quotient projection. -/
@[expose] def forwardMovedSpanProjection (c : Vertex R) :
    forwardMovedSpan R c→*((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R))) :=
  (QuotientGroup.mk' _).comp (inclusion (forwardMovedSpan_le R c))

namespace Source
variable [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
/-- The literal group image is the alternating moved subspace. -/
theorem forward_moved_span_image (c : Vertex R)
    [IsElementaryAbelian 2 ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R)))]
    (ρ : Model.S→*MulAut ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R))))
    (hρ : ∀m:M,ρ (s.projection m)=forwardSpanCentralAction R c m) :
    AddSubgroup.toZModSubmodule 2 (forwardMovedSpanProjection R c).range.toAddSubgroup =
      subspaceCommutator (Offenders.linearize ρ) ⊤ (alternatingGroup (Fin 6)) := by
  let P := localZSpan R c (alpha R)
  let q := QuotientGroup.mk' (center P)
  let S := subspaceCommutator (Offenders.linearize ρ) ⊤ (alternatingGroup (Fin 6))
  have hd (m:M) (z:P) : q (forwardSpanAction R c m z/z)=ρ (s.projection m) (q z)/q z := by
    rw [map_div,hρ,forwardSpanCentralAction_apply]
  have hbound : forwardMovedSpan R c≤(S.toAddSubgroup.toSubgroup'.comap q).map P.subtype := by
    rw [forwardMovedSpan,commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    rw [Ltilde_alpha,s.residual] at hl
    obtain ⟨m,hm,rfl⟩ := hl
    refine ⟨forwardSpanAction R c m ⟨z,hz⟩/⟨z,hz⟩,?_,?_⟩
    · change Additive.ofMul (q (forwardSpanAction R c m ⟨z,hz⟩/⟨z,hz⟩))∈S
      rw [hd]
      exact Submodule.subset_span ⟨s.projection m,s.component_image ▸ mem_map_of_mem s.projection hm,
        Additive.ofMul (q ⟨z,hz⟩),Submodule.mem_top,rfl⟩
    · change embedM R m*z*(embedM R m)⁻¹/z=⁅embedM R m,z⁆
      rw [div_eq_mul_inv,commutatorElement_def]
  apply le_antisymm
  · intro v hv
    change v.toMul∈(forwardMovedSpanProjection R c).range at hv
    obtain ⟨x,hx⟩ := hv
    obtain ⟨z,hz,he⟩ := hbound x.property
    have he' : z=inclusion (forwardMovedSpan_le R c) x := Subtype.ext he
    change Additive.ofMul (q z)∈S at hz
    rw [he'] at hz
    change Additive.ofMul ((forwardMovedSpanProjection R c) x)∈S at hz
    rw [hx] at hz
    exact hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    rw [←s.component_image] at ha
    obtain ⟨m,hm,rfl⟩ := ha
    obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    change ρ (s.projection m) v.toMul/v.toMul∈(forwardMovedSpanProjection R c).range
    rw [←hz]
    refine ⟨⟨⁅embedM R m,(z:FreeAmalgam R)⁆,?_⟩,?_⟩
    · rw [forwardMovedSpan,commutator_comm]
      exact commutator_mem_commutator (by rw [Ltilde_alpha,s.residual];exact mem_map_of_mem (embedM R) hm) z.property
    · change q (⟨⁅embedM R m,(z:FreeAmalgam R)⁆,_⟩:P)=_
      rw [←hd]
      apply congrArg q
      apply Subtype.ext
      change ⁅embedM R m,(z:FreeAmalgam R)⁆=
        embedM R m*(z:FreeAmalgam R)*(embedM R m)⁻¹/(z:FreeAmalgam R)
      rw [div_eq_mul_inv,commutatorElement_def]
end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
/-- The fixed-space preimage is exactly the intrinsic center of the moved group. -/
theorem forward_moved_span_fixed_kernel (c : Vertex R)
    [IsElementaryAbelian 2 ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R)))]
    (ρ : Model.S→*MulAut ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R))))
    (hρ : ∀m:M,ρ (s.projection m)=forwardSpanCentralAction R c m)
    (hfixed : ⁅localZSpan R c (alpha R),localZSpan R c (alpha R)⁆≤
      centralizer (Ltilde R (alpha R):Set (FreeAmalgam R))) :
    (fixedSpace (Offenders.linearize ρ) (alternatingGroup (Fin 6))).toAddSubgroup.toSubgroup'.comap
      (forwardMovedSpanProjection R c)=center (forwardMovedSpan R c) := by
  let P := localZSpan R c (alpha R)
  let P₀ := forwardMovedSpan R c
  let q := forwardMovedSpanProjection R c
  let F := (fixedSpace (Offenders.linearize ρ) (alternatingGroup (Fin 6))).toAddSubgroup.toSubgroup'
  let K := F.comap q
  have hpoint (x:P₀) : q x∈F ↔
      ∀l∈Ltilde R (alpha R),⁅l,(x:FreeAmalgam R)⁆∈centralizer (P:Set (FreeAmalgam R)) := by
    constructor
    · intro hx l hl
      rw [Ltilde_alpha,s.residual] at hl
      obtain ⟨m,hm,rfl⟩ := hl
      have hmA : s.projection m∈alternatingGroup (Fin 6) :=
        s.component_image ▸ mem_map_of_mem s.projection hm
      have he := congrArg Additive.toMul (hx ⟨s.projection m,hmA⟩)
      change ρ (s.projection m) (q x)=q x at he
      rw [hρ] at he
      have he' : QuotientGroup.mk' (center P)
          (forwardSpanAction R c m (inclusion (forwardMovedSpan_le R c) x))=
          QuotientGroup.mk' (center P) (inclusion (forwardMovedSpan_le R c) x) :=
        (forwardSpanCentralAction_apply R c m _).symm.trans he
      have hz := QuotientGroup.eq_iff_div_mem.mp he'
      intro y hy
      have hh := congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
      change y*(embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))=
        (embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))*y at hh
      simpa only [div_eq_mul_inv,commutatorElement_def] using hh
    · intro hx a
      have ha : (a:Model.S)∈L.map s.projection := s.component_image.symm ▸ a.property
      obtain ⟨m,hm,he⟩ := ha
      apply Additive.toMul.injective
      change ρ a (q x)=q x
      rw [←he,hρ]
      change forwardSpanCentralAction R c m
        (QuotientGroup.mk' (center P) (inclusion (forwardMovedSpan_le R c) x))=_
      rw [forwardSpanCentralAction_apply]
      apply QuotientGroup.eq_iff_div_mem.mpr
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hh := hx (embedM R m) (by
        rw [Ltilde_alpha,s.residual]
        exact mem_map_of_mem (embedM R) hm) y y.property
      change (y:FreeAmalgam R)*(embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))=
        (embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))*(y:FreeAmalgam R)
      simpa only [div_eq_mul_inv,commutatorElement_def] using hh
  have hKP : K.map P₀.subtype≤P := (map_subtype_le _).trans (forwardMovedSpan_le R c)
  have hKL : ⁅K.map P₀.subtype,Ltilde R (alpha R)⁆≤centralizer (P:Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro l hl _ ⟨x,hx,rfl⟩
    exact (hpoint x).mp hx l hl
  have hKC : K.map P₀.subtype≤centralizer (P₀:Set (FreeAmalgam R)) :=
    (commutator_centralizes_iff_centralizes_moved P _ _ hKP hfixed).mp hKL
  have hAC : (center P₀).map P₀.subtype≤centralizer (P₀:Set (FreeAmalgam R)) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hAL : ⁅(center P₀).map P₀.subtype,Ltilde R (alpha R)⁆≤centralizer (P:Set (FreeAmalgam R)) :=
    (commutator_centralizes_iff_centralizes_moved P _ _
      ((map_subtype_le _).trans (forwardMovedSpan_le R c)) hfixed).mpr hAC
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hKC (mem_map_of_mem P₀.subtype hx) y y.property)
  · intro hx
    apply (hpoint x).mpr
    intro l hl
    rw [commutator_comm] at hAL
    exact hAL (commutator_mem_commutator hl (mem_map_of_mem P₀.subtype hx))
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
theorem forward_moved_span_natural_coordinates_of_section (c : Vertex R)
    [IsElementaryAbelian 2 ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R)))]
    (ρ : Model.S→*MulAut ((localZSpan R c (alpha R))⧸center (localZSpan R c (alpha R))))
    (hρ : ∀m:M,ρ (s.projection m)=forwardSpanCentralAction R c m)
    (hfixed : ⁅localZSpan R c (alpha R),localZSpan R c (alpha R)⁆≤
      centralizer (Ltilde R (alpha R):Set (FreeAmalgam R)))
    (sec : MovedSection (Offenders.linearize ρ) (alternatingGroup (Fin 6)))
    (hn : IsSymmetricNatural sec.action 6) :
    ∃ (e : ((forwardMovedSpan R c)⧸center (forwardMovedSpan R c))≃*
        Multiplicative (BinaryPermutation.natural (Fin 6))) (τ : Model.S≃*Model.S),
      ∀(m:M)(x:forwardMovedSpan R c),
        (e (QuotientGroup.mk' (center (forwardMovedSpan R c)) (forwardMovedSpanAction R c m x))).toAdd=
          BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
            (e (QuotientGroup.mk' (center (forwardMovedSpan R c)) x)).toAdd := by
  obtain ⟨E⟩ := hn
  let P₀ := forwardMovedSpan R c
  let q := forwardMovedSpanProjection R c
  have himage : AddSubgroup.toZModSubmodule 2 q.range.toAddSubgroup=sec.space.toSubmodule :=
    (s.forward_moved_span_image c ρ hρ).trans sec.space_eq.symm
  let r : Additive P₀→+sec.space.toSubmodule := {
    toFun := fun x => ⟨Additive.ofMul (q x.toMul),by
      rw [←himage]
      exact ⟨x.toMul,rfl⟩⟩
    map_zero' := by
      apply Subtype.ext
      exact congrArg Additive.ofMul (map_one q)
    map_add' := by
      intro x y
      apply Subtype.ext
      exact congrArg Additive.ofMul (map_mul q x.toMul y.toMul) }
  have hr : Function.Surjective r := by
    intro v
    have hv : v.val.toMul∈q.range := by
      change v.val∈AddSubgroup.toZModSubmodule 2 q.range.toAddSubgroup
      rw [himage]
      exact v.property
    obtain ⟨x,hx⟩ := hv
    exact ⟨Additive.ofMul x,Subtype.ext (congrArg Additive.ofMul hx)⟩
  let f : P₀→*Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    ((E.linearEquiv.toLinearMap.comp sec.central.toSubmodule.mkQ).toAddMonoidHom.comp r).toMultiplicativeRight
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,hx⟩ := E.linearEquiv.surjective.comp
      (sec.central.toSubmodule.mkQ_surjective.comp hr) v.toAdd
    exact ⟨x.toMul,congrArg Multiplicative.ofAdd hx⟩
  have hk : f.ker=center P₀ := by
    ext x
    change E.linearEquiv (sec.central.toSubmodule.mkQ (r (Additive.ofMul x)))=0 ↔ x∈center P₀
    rw [E.linearEquiv.map_eq_zero_iff,←LinearMap.mem_ker,Submodule.ker_mkQ,sec.central_eq]
    rw [←s.forward_moved_span_fixed_kernel c ρ hρ hfixed]
    change (∀a:alternatingGroup (Fin 6),sec.space.toRepresentation a (r (Additive.ofMul x))=
      r (Additive.ofMul x)) ↔
        ∀a:alternatingGroup (Fin 6),Offenders.linearize ρ a (Additive.ofMul (q x))=Additive.ofMul (q x)
    constructor
    · intro hx a
      exact congrArg Subtype.val (hx a)
    · intro hx a
      exact Subtype.ext (hx a)
  let e : (P₀⧸center P₀)≃*Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x:P₀) : e (QuotientGroup.mk' (center P₀) x)=f x := rfl
  have hract (m:M) (x:P₀) : r (Additive.ofMul (forwardMovedSpanAction R c m x))=
      sec.space.toRepresentation (s.projection m) (r (Additive.ofMul x)) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change q (forwardMovedSpanAction R c m x)=ρ (s.projection m) (q x)
    rw [hρ]
    change QuotientGroup.mk' (center (localZSpan R c (alpha R)))
        (inclusion (forwardMovedSpan_le R c) (forwardMovedSpanAction R c m x))=
      forwardSpanCentralAction R c m
        (QuotientGroup.mk' (center (localZSpan R c (alpha R))) (inclusion (forwardMovedSpan_le R c) x))
    rw [forwardSpanCentralAction_apply]
    rfl
  refine ⟨e,E.groupEquiv,?_⟩
  intro m x
  rw [he,he]
  change E.linearEquiv (sec.central.toSubmodule.mkQ (r (Additive.ofMul (forwardMovedSpanAction R c m x))))=_
  rw [hract,←sec.central.quotientRepresentation_mk]
  exact E.intertwines (s.projection m) _
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
@[expose] def ForwardMovedSpanNaturalData (c : Vertex R) : Prop :=
  ∃ (e : ((forwardMovedSpan R c)⧸center (forwardMovedSpan R c))≃*
        Multiplicative (BinaryPermutation.natural (Fin 6))) (τ : Model.S≃*Model.S),
    ∀(m:M)(x:forwardMovedSpan R c),
      (e (QuotientGroup.mk' (center (forwardMovedSpan R c)) (forwardMovedSpanAction R c m x))).toAdd=
        BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))
          (e (QuotientGroup.mk' (center (forwardMovedSpan R c)) x)).toAdd

theorem forward_moved_span_natural_data
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    s.ForwardMovedSpanNaturalData (p.walk.getVert 2) := by
  obtain ⟨hEA,ρ,hρ,_,sec,hn⟩ := s.forward_span_natural_data h u hfull hsq hb p
  let := hEA
  exact s.forward_moved_span_natural_coordinates_of_section _ ρ hρ
    (((s.forward_span_derived_eq_line h u hfull hb p).2.2.1).trans
      (centralizer_le (Ltilde_le_stabilizer _))) sec hn

theorem forward_moved_span_central_quotient_card
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    Nat.card ((forwardMovedSpan R (p.walk.getVert 2))⧸center (forwardMovedSpan R (p.walk.getVert 2)))=16 := by
  obtain ⟨E,_,_⟩ := s.forward_moved_span_natural_data h u hfull hsq hb p
  rw [Nat.card_congr E.toEquiv]
  change Nat.card (BinaryPermutation.natural (Fin 6))=16
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  rfl

theorem forward_moved_span_derived_eq
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    let P₀ := forwardMovedSpan R (p.walk.getVert 2)
    ⁅P₀,P₀⁆=⁅P,P⁆ ∧ Nat.card (⁅P₀,P₀⁆:Subgroup (FreeAmalgam R))=2 := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let P₀ := forwardMovedSpan R (p.walk.getVert 2)
  have hc := s.forward_moved_span_central_quotient_card h u hfull hsq hb p
  have hcard : Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam R))=2 :=
    (s.forward_span_derived_eq_line h u hfull hb p).2.1
  have hle : ⁅P₀,P₀⁆≤⁅P,P⁆ := commutator_mono (forwardMovedSpan_le R _) (forwardMovedSpan_le R _)
  let : Finite (⁅P,P⁆:Subgroup (FreeAmalgam R)) := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (⁅P₀,P₀⁆:Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective hle)
  have hne : (⁅P₀,P₀⁆:Subgroup (FreeAmalgam R))≠⊥ := by
    intro he
    have he' : _root_.commutator P₀=⊥ := by
      apply map_injective P₀.subtype_injective
      rw [map_subtype_commutator,Subgroup.map_bot]
      exact he
    have hz := (_root_.commutator_eq_bot_iff_center_eq_top P₀).mp he'
    rw [←index_eq_card,hz,index_top] at hc
    omega
  have hpos := (one_lt_card_iff_ne_bot (⁅P₀,P₀⁆:Subgroup (FreeAmalgam R))).mpr hne
  have he : (⁅P₀,P₀⁆:Subgroup (FreeAmalgam R))=⁅P,P⁆ := eq_of_le_of_card_ge hle (by omega)
  exact ⟨he,he.symm ▸ hcard⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

theorem reducedSource_block_or_forward_moved_span_natural
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      ((originalSource d hm).reduce r).ForwardMovedSpanNaturalData (p.walk.getVert 2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_moved_span_natural_data (reduced_nativeCentralLayer d hm r) _ hf
      ((d.sqtk.subgroup J).subgroup r.overgroup) hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

theorem reducedSource_block_or_forward_moved_span_derived
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      (let P := localZSpan r.radical (p.walk.getVert 2) (alpha r.radical)
       let P₀ := forwardMovedSpan r.radical (p.walk.getVert 2)
       ⁅P₀,P₀⁆=⁅P,P⁆ ∧ Nat.card (⁅P₀,P₀⁆:Subgroup (FreeAmalgam r.radical))=2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_moved_span_derived_eq (reduced_nativeCentralLayer d hm r) _ hf
      ((d.sqtk.subgroup J).subgroup r.overgroup) hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
