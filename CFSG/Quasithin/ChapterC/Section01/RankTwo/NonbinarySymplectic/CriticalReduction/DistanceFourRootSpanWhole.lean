module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.SmallCodimension
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.SpecificGroups.SymplecticFour.FourLongRoots

/-!
# The whole literal root-offender span is natural

The retained endpoint offender has order q. Its action on the recognized
natural moved section therefore has fixed codimension at most n, which
identifies its image in those coordinates with a full long root. Four
conjugates of that same actor generate the symplectic group. The resulting
4n budget is already attained by the natural moved section, while the full
quotient has zero fixed space. Thus the whole quotient is the moved space.

All quotient coordinates, the full kernel, the actual endpoint conjugator,
and both seed budgets are retained. The whole natural equivalence uses the
same acting-group isomorphism as the recognized moved-section equivalence.
Source: MS93 (5.12), printed p.927, with (1.1)(ii)(1) and (3.3), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem four_conjugates_of_field_sized_offender
    (E : BinaryField) (hE : 2 < Nat.card E.Carrier)
    (A : Subgroup (Sp E.Carrier)) (hA : IsOffender (binarySymplectic E) A)
    (hc : Nat.card A=Nat.card E.Carrier) :
    ∃ g : Fin 4 → Sp E.Carrier,
      (⨆ i, A.map (MulAut.conj (g i)).toMonoidHom)=⊤ := by
  have hr : rank A=E.degree := by
    rw [rank,hc,E.card_eq,Nat.log_pow (by decide : 1<2)]
  have hd : fixedCodim (SymplecticConjugatePair.binaryNatural (F := E.Carrier)) A <
      2*E.degree := by
    have hh := hA.2
    change fixedCodim (SymplecticConjugatePair.binaryNatural (F := E.Carrier)) A ≤ rank A at hh
    rw [hr] at hh
    have hp := E.degree_pos
    omega
  let := hA.1.2
  obtain ⟨g,hg⟩ := SymplecticConjugatePair.elementary_conjugate_radical
    E.card_eq E.degree_pos A
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBd : fixedCodim (SymplecticConjugatePair.binaryNatural (F := E.Carrier)) B <
      2*E.degree := by simpa only [B,fixedCodim_map_conj] using hd
  have hplane : B ≤ SymplecticConjugatePair.planeRadical := by
    rcases hg with hp | hp
    · by_contra hn
      exact (not_lt_of_ge
        (SymplecticConjugatePair.NaturalBounds.point_outside_plane_fixedCodim
          E.card_eq hp hn)) hBd
    · exact hp
  have hne : fixedSpace (SymplecticConjugatePair.binaryNatural (F := E.Carrier)) B ≠
      (plane E.Carrier).restrictScalars (ZMod 2) := by
    intro he
    have hh := fixedCodim_add_finrank
      (SymplecticConjugatePair.binaryNatural (F := E.Carrier)) B
    rw [he,SymplecticConjugatePair.finrank_binary_plane E.card_eq,
      SymplecticConjugatePair.finrank_vector E.card_eq] at hh
    omega
  obtain ⟨T,hT,hBT⟩ :=
    SymplecticConjugatePair.exists_sylowTransvectionRoot_of_fixedSpace_ne hplane hne
  have hBT' : B=T := Subgroup.eq_of_le_of_card_ge hBT (by
    rw [hT.card,show Nat.card B=Nat.card A from
      Subgroup.card_map_of_injective (MulAut.conj g).injective,hc])
  obtain ⟨k,hk⟩ := hT.2
  let r := k⁻¹*g
  have hroot : A.map (MulAut.conj r).toMonoidHom=RootSubgroup.group 0 := by
    calc
      _ = B.map (MulAut.conj k⁻¹).toMonoidHom := by
        dsimp only [B]
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [r,MulAut.conj_apply,mul_assoc]
      _ = ((RootSubgroup.group 0).map (MulAut.conj k).toMonoidHom).map
          (MulAut.conj k⁻¹).toMonoidHom := by rw [hBT',hk]
      _ = _ := by
        rw [Subgroup.map_map]
        have he : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom=
            MonoidHom.id (Sp E.Carrier) := by ext x; simp [MulAut.conj_apply,mul_assoc]
        rw [he,Subgroup.map_id]
  obtain ⟨v,hv⟩ := FourLongRoots.exists_four_conjugates_generate hE
  refine ⟨fun i => v i*r,?_⟩
  have he (i : Fin 4) : A.map (MulAut.conj (v i*r)).toMonoidHom=
      (RootSubgroup.group 0).map (MulAut.conj (v i)).toMonoidHom := by
    rw [←hroot,Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  simpa only [he] using hv

private theorem whole_of_field_sized_offender
    {G V₀ : Type*} [Group G] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (σ : Representation (ZMod 2) G V₀) (E : BinaryField)
    (hE : 2 < Nat.card E.Carrier)
    (e : ActionEquiv ((MovedSection.ofNormal σ ⊤).action.comp
      (⊤ : Subgroup G).subtype) (binarySymplectic E))
    (hzero : fixedSpace σ ⊤=⊥) (A : Subgroup G)
    (hA : IsOffender σ A) (hc : Nat.card A=Nat.card E.Carrier) :
    subspaceCommutator σ ⊤ ⊤=⊤ ∧
      ∃ eW : ActionEquiv σ (binarySymplectic E),
        eW.groupEquiv=topEquiv.symm.trans e.groupEquiv := by
  let s := MovedSection.ofNormal σ (⊤ : Subgroup G)
  let α : G ≃* Sp E.Carrier := topEquiv.symm.trans e.groupEquiv
  let e₀ : ActionEquiv s.action (binarySymplectic E) := {
    groupEquiv := α
    linearEquiv := e.linearEquiv
    intertwines g v := e.intertwines ⟨g,mem_top g⟩ v }
  have hmove : IsOffender s.action A := by
    refine ⟨hA.1,?_⟩
    exact ((Nat.le_add_right _ _).trans
      ((fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A).trans
        (fixedCodim_subrepresentation_le σ s.space A))).trans hA.2
  let A' := A.map α.toMonoidHom
  have hA' : IsOffender (binarySymplectic E) A' :=
    hmove.map_equivariant s.action (binarySymplectic E) α.toMonoidHom α.injective
      e₀.linearEquiv e₀.intertwines
  have hc' : Nat.card A'=Nat.card E.Carrier := by
    dsimp only [A']
    rw [Subgroup.card_map_of_injective α.injective,hc]
  obtain ⟨g,hg⟩ := four_conjugates_of_field_sized_offender E hE A' hA' hc'
  have hgen : (⨆ i, A.map (MulAut.conj (α.symm (g i))).toMonoidHom)=⊤ := by
    apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
    rw [Subgroup.map_iSup,Subgroup.map_top_of_surjective _ α.surjective]
    have he (i : Fin 4) : (A.map (MulAut.conj (α.symm (g i))).toMonoidHom).map
        α.toMonoidHom=A'.map (MulAut.conj (g i)).toMonoidHom := by
      dsimp only [A']
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    simpa only [he] using hg
  have hr : rank A=E.degree := by
    rw [rank,hc,E.card_eq,Nat.log_pow (by decide : 1<2)]
  have hupper : Module.finrank (ZMod 2) V₀ ≤ 4*E.degree := by
    have hh := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ A
      (fun i : Fin 4 => α.symm (g i)) hgen.ge
    rw [Fintype.card_fin] at hh
    have hd := fixedCodim_add_finrank σ ⊤
    rw [hzero,finrank_bot,add_zero] at hd
    rw [←hd]
    exact hh.trans (Nat.mul_le_mul_left 4 (by simpa only [hr] using hA.2))
  have hlower : 4*E.degree ≤ Module.finrank (ZMod 2) s.space.toSubmodule := by
    have he : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)=4*E.degree :=
      e.linearEquiv.finrank_eq.trans (SymplecticConjugatePair.finrank_vector E.card_eq)
    rw [←he]
    exact Submodule.finrank_quotient_le _
  have hwhole : s.space.toSubmodule=⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm s.space.toSubmodule.finrank_le
      (hupper.trans hlower))
  refine ⟨s.space_eq.symm.trans hwhole,?_⟩
  let p : s.space.toSubmodule →ₗ[ZMod 2] Vector E.Carrier :=
    e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  have hp : Function.Bijective p := by
    refine ⟨LinearMap.ker_eq_bot.mp ?_,
      e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)⟩
    apply bot_unique
    intro v hv
    have hz : s.central.toSubmodule.mkQ v=0 :=
      e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    have hm := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hz
    rw [s.central_eq] at hm
    have hvfix : v.val ∈ fixedSpace σ ⊤ := fun g => congrArg Subtype.val (hm g)
    have hvzero : v.val=0 := by simpa only [hzero,Submodule.mem_bot] using hvfix
    exact Subtype.ext hvzero
  let pe : s.space.toSubmodule ≃ₗ[ZMod 2] Vector E.Carrier :=
    LinearEquiv.ofBijective p hp
  let ve : s.space.toSubmodule ≃ₗ[ZMod 2] V₀ :=
    LinearEquiv.ofBijective s.space.toSubmodule.subtype
      ⟨Subtype.val_injective,fun v => ⟨⟨v,hwhole.symm ▸ Submodule.mem_top⟩,rfl⟩⟩
  refine ⟨⟨α,ve.symm.trans pe,?_⟩,rfl⟩
  intro g v
  change p (ve.symm (σ g v))=binarySymplectic E (α g) (p (ve.symm v))
  have he : ve.symm (σ g v)=s.space.toRepresentation g (ve.symm v) := by
    apply ve.injective
    rw [ve.apply_symm_apply]
    change σ g v=σ g (ve (ve.symm v))
    rw [ve.apply_symm_apply]
  rw [he]
  exact e₀.intertwines g (s.central.toSubmodule.mkQ (ve.symm v))

/-- The original full root-offender quotient with a natural equivalence on
the whole carrier, using its retained moved-section group marking. -/
@[expose] def distanceFourRootSpanWhole {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (a e z : Vertex R) (n : ℕ) : Prop :=
  let W := localZSpan R e a
  let D := W ⊓ B R a (geometry.Z_normal a)
  ∃ E : BinaryField, E.degree=n ∧
    ∃ f : stabilizer R a →* Sp E.Carrier,
      Function.Surjective f ∧ f.ker.map (stabilizer R a).subtype=Q R a ∧
      ∃ hD : (D.subgroupOf W).Normal,
        letI := hD
        ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
          letI := hEA
          ∃ σ : Representation (ZMod 2) (Sp E.Carrier) (Additive (W ⧸ D.subgroupOf W)),
            Function.Injective σ ∧
            ∃ c : BinaryConjugationSection (stabilizer R a) W D (σ.comp f),
              (∀ w : W, (c.coordinates w).toAdd=
                Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
              IsOffender σ (((Z R z).subgroupOf (stabilizer R a)).map f) ∧
              fixedSpace σ ⊤=⊥ ∧
              IsIrrPlus σ ⊤ (subspaceCommutator σ ⊤ ⊤) ∧
              subspaceCommutator σ ⊤ ⊤=⊤ ∧
              ∃ Eₙ : BinaryField, Eₙ.degree=n ∧
                ∃ eₙ : ActionEquiv ((MovedSection.ofNormal σ ⊤).action.comp
                    (⊤ : Subgroup (Sp E.Carrier)).subtype) (binarySymplectic Eₙ),
                  ∃ eW : ActionEquiv σ (binarySymplectic Eₙ),
                    eW.groupEquiv=topEquiv.symm.trans eₙ.groupEquiv

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual root endpoint offender fills the whole midpoint span quotient,
with all original full-kernel coordinates and both natural markings retained. -/
theorem Input.replacement_distance_four_root_span_whole
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfirst : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    distanceFourRootSpanWhole geometry a (path.walk.getVert 2) z n := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hdata⟩ :=
    h.replacement_distance_four_root_span_natural d path hb g hg hga hfixed hfirst hlast
  let := hD
  obtain ⟨hEA,hdata⟩ := hdata
  let := hEA
  obtain ⟨σ,hfaith,c,hcoord,hactor,hzero,hIrr,Eₙ,hEₙ,⟨eₙ⟩⟩ := hdata
  let := finite_stabilizer d.radical a
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let S := stabilizer d.radical a
  let : Finite W := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let A := ((Z d.radical z).subgroupOf S).map f
  have hk : f.ker=(Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  have hc : Nat.card A=Nat.card Eₙ.Carrier := by
    change Nat.card (((Z d.radical z).subgroupOf S).map f)=Nat.card Eₙ.Carrier
    rw [←relIndex_ker,hk,relIndex_subgroupOf
      (path.endpoint_Z_le_start_stabilizer (by omega))]
    rw [(h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path).2,
      Eₙ.card_eq,hEₙ]
    exact h.field_card
  have hEn : 2 < Nat.card Eₙ.Carrier := by
    rw [Eₙ.card_eq,hEₙ]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨hwhole,eW,heW⟩ := whole_of_field_sized_offender σ Eₙ hEn eₙ hzero A hactor hc
  exact ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor,hzero,hIrr,hwhole,
    Eₙ,hEₙ,eₙ,eW,heW⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
