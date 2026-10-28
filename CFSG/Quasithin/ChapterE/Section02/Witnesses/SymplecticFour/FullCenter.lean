module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.FourAxes

/-!
# The full central-plane branch of the original Sp4 witness

The two central root axes and their opposites generate the whole symplectic
component. The opposition matrix is therefore an internal conjugator. The
original Sylow and Borel marks produce the literal two-conjugate Pair, and
simplicity makes the relative Borel core trivial. Every model, central-root
mark and quotient map is retained for the E.2.9 lift.

Source: Aschbacher–Smith E.2.7, pp.219–220. This closes the full-center case;
smaller V still requires the source's subgroup recognition argument.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate DiagramAutomorphisms
open ChapterB Representation.OneCohomology.SymplecticFour
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] [Field F] [Finite F] [CharP F 2] in
private theorem map_conjugate_pair {K:Type*} [Group K] (f:K→*G) (W:Subgroup K) (g:K) :
    (W⊔W.map (MulAut.conj g).toMonoidHom).map f=
      W.map f⊔(W.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- A symplectic source witness retaining the actual coefficient field. Field
cardinality supplies its degree, without changing any subgroup or action. -/
structure NativeWitness (T:Sylow 2 G) (M V:Subgroup G) (F:Type*) [Field F] where
  pair : QuotientLift.Pair T M V
  model : pair.subgroup≃*Sp F
  sylow_model : (pair.sylow:Subgroup pair.subgroup).map model.toMonoidHom=unipotent
  borel_model : (M.subgroupOf pair.subgroup).map model.toMonoidHom=borel
  corefree : (M.subgroupOf pair.subgroup).normalCore=⊥
  center_model : (V.subgroupOf pair.subgroup).map model.toMonoidHom≤
    (center (unipotent (F:=F))).map (unipotent (F:=F)).subtype
  not_long : ¬(V.subgroupOf pair.subgroup).map model.toMonoidHom≤RootSubgroup.group 0
  not_short : ¬(V.subgroupOf pair.subgroup).map model.toMonoidHom≤RootSubgroup.group 4

omit [Finite F] in
private theorem parameter_not_long :
    ¬(CentralRootGeometry.parameter (F:=F)).range≤RootSubgroup.group 0 := by
  intro h
  have h4:rootElement 4 (1:F)∈(CentralRootGeometry.parameter (F:=F)).range :=
    ⟨(1,Multiplicative.ofAdd 1),by simp [CentralRootGeometry.parameter_apply,RootSubgroup.element_zero]⟩
  obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 0 _).mp (h h4)
  have he:=congrArg (fun x:Sp F=>x.val (Sum.inl 0) (Sum.inr 1)) ha
  change rootMatrix 0 a (Sum.inl 0) (Sum.inr 1)=rootMatrix 4 (1:F) (Sum.inl 0) (Sum.inr 1) at he
  simp [rootMatrix,Matrix.fromBlocks,Matrix.single] at he

omit [Finite F] in
private theorem parameter_not_short :
    ¬(CentralRootGeometry.parameter (F:=F)).range≤RootSubgroup.group 4 := by
  intro h
  have h0:rootElement 0 (1:F)∈(CentralRootGeometry.parameter (F:=F)).range :=
    ⟨(Multiplicative.ofAdd 1,1),by simp [CentralRootGeometry.parameter_apply,RootSubgroup.element_zero]⟩
  obtain ⟨a,ha⟩ := (RootSubgroup.mem_group_iff 4 _).mp (h h0)
  have he:=congrArg (fun x:Sp F=>x.val (Sum.inl 0) (Sum.inr 0)) ha
  change rootMatrix 4 a (Sum.inl 0) (Sum.inr 0)=rootMatrix 0 (1:F) (Sum.inl 0) (Sum.inr 0) at he
  simp [rootMatrix,Matrix.fromBlocks,Matrix.single] at he

/-- The actual full-center branch has a source pair equal to the original
simple component, with its prescribed Sylow and Borel markings. -/
theorem source_full_center_pair {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) (hVL:V≤L)
    (hcenter:V.comap (L.subtype.comp e.toMonoidHom)=CentralRootGeometry.parameter.range) :
    ∃w:NativeWitness T (minimalParabolicMax T hP) V F, w.pair.subgroup=L := by
  let f:=L.subtype.comp e.toMonoidHom
  let W:=V.comap f
  let M:=minimalParabolicMax T hP
  have hf:Function.Injective f:=L.subtype_injective.comp e.injective
  have hfr:f.range=L := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hmap:W.map f=V := by rw [map_comap_eq,hfr,inf_eq_right.mpr hVL]
  have hwhole:oppositePair W=⊤ := by
    change oppositePair (V.comap f)=⊤
    rw [hcenter]
    exact oppositePair_parameter_range
  have hpair:V⊔V.map (MulAut.conj (f opposition)).toMonoidHom=L := by
    have h:=congrArg (fun A:Subgroup (Sp F)=>A.map f) hwhole
    rw [oppositePair,map_conjugate_pair,hmap,←MonoidHom.range_eq_map,hfr] at h
    exact h
  let g:L:=e opposition
  have hg:V.subgroupOf L⊔(V.subgroupOf L).map (MulAut.conj g).toMonoidHom=⊤ := by
    apply map_injective L.subtype_injective
    rw [map_conjugate_pair,map_subgroupOf_eq_of_le hVL,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hpair
  let P: Sylow 2 L := (unipotentSylow hF hn.le).mapSurjective
    (f:=e.toMonoidHom) e.surjective
  have hPmap:(P:Subgroup L).map L.subtype=(T:Subgroup G)⊓L := by
    change (unipotent.map e.toMonoidHom).map L.subtype=_
    rw [map_map,←hmark,map_comap_eq,hfr,inf_comm]
  have hcore:(M.subgroupOf L).normalCore=⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf L).normalCore inferInstance
      with h|h
    · exact h
    · have hLM:L≤M := by
        intro x hx
        have hh:(⟨x,hx⟩:L)∈(M.subgroupOf L).normalCore := h ▸ mem_top _
        exact (M.subgroupOf L).normalCore_le hh
      have hMtop:M=⊤ := top_unique (hgen ▸ sup_le hLM (minimalParabolicMax_spec T hP).2)
      exact ((minimalParabolicMax_spec T hP).1.ne_top hMtop).elim
  let w:QuotientLift.Pair T M V := {
    subgroup:=L
    le:=hVL
    conjugator:=g
    generate:=hg
    sylow:=P
    sylow_eq:=hPmap
    core_two_closed:=by rw [hcore];exact ⟨default,inferInstance⟩ }
  have hVmodel:(V.subgroupOf L).map e.symm.toMonoidHom=CentralRootGeometry.parameter.range := by
    rw [map_equiv_eq_comap_symm']
    exact hcenter
  refine ⟨{
    pair:=w
    model:=e.symm
    sylow_model:=?_
    borel_model:=?_
    corefree:=hcore
    center_model:=?_
    not_long:=?_
    not_short:=?_ },rfl⟩
  · change (unipotent.map e.toMonoidHom).map e.symm.toMonoidHom=unipotent
    rw [map_map]
    simp
  · change (M.subgroupOf L).map e.symm.toMonoidHom=borel
    rw [map_equiv_eq_comap_symm']
    exact Structure.SymplecticFour.source_borel_intersection hF hn T hP L e hmark hgen
  · change (V.subgroupOf L).map e.symm.toMonoidHom≤_
    rw [hVmodel,CentralRootGeometry.parameter_range]
  · change ¬(V.subgroupOf L).map e.symm.toMonoidHom≤_
    rw [hVmodel]
    exact parameter_not_long
  · change ¬(V.subgroupOf L).map e.symm.toMonoidHom≤_
    rw [hVmodel]
    exact parameter_not_short

/-- Original source endpoint when V reaches the full central-root plane's
cardinality. The pair, internal conjugator, model and all marks are constructed. -/
theorem source_pair_of_full_card {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
    (hJ:minimalParabolicCore T hP=⊥)
    (L:Subgroup G) [L.Normal] [IsSimpleGroup L] (e:L≃*commutator (Sp F))
    (hgen:L⊔(T:Subgroup G)=⊤)
    (V:Subgroup G) [IsElementaryAbelian 2 V] (hVT:V≤T)
    [(V.subgroupOf T).Normal]
    (hVM:V≤(minimalParabolicMax T hP).pCoreIn 2) (hr:1<Group.rank V)
    (hcard:(Nat.card F)^2≤Nat.card V) :
    ∃w:NativeWitness T (minimalParabolicMax T hP) V F, w.pair.subgroup=L := by
  obtain ⟨e',hT,_,hVL,hmap,hcenter,_,_⟩:=
    Structure.SymplecticFour.source_derived_geometry hF hn T hP hJ L e hgen V hVT hVM hr
  let f:=L.subtype.comp e'.toMonoidHom
  have hf:Function.Injective f:=L.subtype_injective.comp e'.injective
  have hc:Nat.card (CentralRootGeometry.parameter (F:=F)).range=(Nat.card F)^2 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (CentralRootGeometry.parameter_injective (F:=F))).toEquiv,Nat.card_prod]
    change Nat.card F*Nat.card F=Nat.card F^2
    exact (pow_two _).symm
  have hcw:Nat.card (V.comap f)=Nat.card V := by
    calc
      Nat.card (V.comap f)=Nat.card ((V.comap f).map f):=
        (card_map_of_injective hf).symm
      _=Nat.card V:=congrArg (fun D:Subgroup G=>Nat.card D) hmap
  have hfull:V.comap f=CentralRootGeometry.parameter.range := by
    apply eq_of_le_of_card_ge
    · exact hcenter.trans_eq CentralRootGeometry.parameter_range.symm
    · rw [hc,hcw]
      exact hcard
  exact source_full_center_pair hF hn T hP L e' hT hgen V hVL hfull

/-- The actual quotient model used by the E.2.9 lift and E.2.15 bound. -/
def NativeWitness.quotientModel {T:Sylow 2 G} {M V:Subgroup G}
    (w:NativeWitness T M V F) :
    (w.pair.subgroup⧸(M.subgroupOf w.pair.subgroup).normalCore)≃*Sp F :=
  ((QuotientGroup.quotientMulEquivOfEq w.corefree).trans QuotientGroup.quotientBot).trans w.model

omit [Finite G] [Finite F] [CharP F 2] in
@[simp] theorem NativeWitness.quotientModel_mk {T:Sylow 2 G} {M V:Subgroup G}
    (w:NativeWitness T M V F) (x:w.pair.subgroup) :
    w.quotientModel (QuotientGroup.mk' (M.subgroupOf w.pair.subgroup).normalCore x)=w.model x := rfl

omit [Finite G] [CharP F 2] in
/-- Literal quotient-center input of `Pair.cubicRatio_lt_two_symplectic`. -/
theorem NativeWitness.quotient_center {T:Sylow 2 G} {M V:Subgroup G}
    (w:NativeWitness T M V F) {n:ℕ} (hF:Nat.card F=2^n) (hn:1≤n) :
    (V.subgroupOf w.pair.subgroup).map (w.quotientModel.toMonoidHom.comp
      (QuotientGroup.mk' (M.subgroupOf w.pair.subgroup).normalCore))≤
      (center (unipotentSylow hF hn)).map (unipotentSylow hF hn:Subgroup (Sp F)).subtype := by
  have he:w.quotientModel.toMonoidHom.comp
      (QuotientGroup.mk' (M.subgroupOf w.pair.subgroup).normalCore)=w.model.toMonoidHom := by
    apply MonoidHom.ext
    exact w.quotientModel_mk
  rw [he]
  exact w.center_model

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
