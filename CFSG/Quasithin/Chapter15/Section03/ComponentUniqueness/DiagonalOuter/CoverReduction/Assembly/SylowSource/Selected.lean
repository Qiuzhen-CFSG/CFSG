module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.SymmetricPairMarking.NormalSubgroups
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.SylowSource.Recognition

/-!
# Cubic factors of the selected actual Sylow normalizer

The selected dihedral section acts faithfully on the original natural module.
This recovers the reflection's opposite-plane fixation after construction
coordinates have been forgotten. Its component-factor commutator vanishes on
the odd Sylow. A nontrivial fixed component cubic then identifies the first
axis of any aligned S3 times S3 coordinates. The chosen Sylow, component,
and both involutions remain the literal source subgroups and elements.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open scoped MatrixGroups
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- The chosen actual dihedral section remains faithful on the natural module. -/
theorem source_selected_natural_faithful {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r) :
    Function.Injective (d.action.actor.comp
      ((inclusion d.sylow_le).comp b.lift.dihedral.sectionMap)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hk : inclusion d.sylow_le (b.lift.dihedral.sectionMap x) ∈ d.action.actor.ker := hx
  rw [d.action.ker_actor] at hk
  have hr := (natural_kernel_T s h r).le
    ⟨(b.lift.dihedral.sectionMap x).property,hk⟩
  rw [r.cover.residual_core] at hr
  have hp : b.lift.dihedral.projection (b.lift.dihedral.sectionMap x)=1 := by
    change b.lift.dihedral.sectionMap x ∈ b.lift.dihedral.projection.ker
    rw [b.lift.dihedral.kernel]
    exact hr.2
  exact mem_bot.mpr ((b.lift.dihedral.rightInverse x).symm.trans hp)

/-- The first reflection of any actual Sylow result fixes the opposite plane. -/
theorem source_selected_first_fixes_second {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r) :
    (b.lift.dihedral.firstReflection : G) ∈ centralizer (r.cover.borel.W₂ : Set G) := by
  let u := b.lift.dihedral.sectionMap (.r 1)
  let t := b.lift.dihedral.firstReflection
  let f := b.lift.dihedral.halfTurn
  have hswap : (d.action.actor (inclusion d.sylow_le u)).right ≠1 :=
    faithful_dihedral_rotation_swaps _ (source_selected_natural_faithful s h r b)
  have humap : r.cover.borel.W₁.map (MulAut.conj (u : G)).toMonoidHom = r.cover.borel.W₂ := by
    have hidx (i : OrthogonalPlaneIndex) (hi : i≠1) :
        i=Multiplicative.ofAdd (1 : ZMod 2) := by
      revert i
      decide +kernel
    rcases r.cover.borel.planes with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · rw [h₁,h₂]
      change (d.action.plane 1).map (MulAut.conj ((inclusion d.sylow_le u : d.M) : G)).toMonoidHom =
        d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))
      rw [cyclic_plane_map,hidx _ hswap,mul_one]
    · rw [h₁,h₂]
      change (d.action.plane (Multiplicative.ofAdd (1 : ZMod 2))).map
        (MulAut.conj ((inclusion d.sylow_le u : d.M) : G)).toMonoidHom = d.action.plane 1
      rw [cyclic_plane_map,hidx _ hswap]
      rfl
  have hk : u⁻¹*t*u=t*f := by
    dsimp only [t,f]
    rw [←b.lift.dihedral.sectionMap_sr_zero,←b.lift.dihedral.sectionMap_r_two]
    change (b.lift.dihedral.sectionMap (.r 1))⁻¹*b.lift.dihedral.sectionMap (.sr 0)*
      b.lift.dihedral.sectionMap (.r 1)=
      b.lift.dihedral.sectionMap (.sr 0)*b.lift.dihedral.sectionMap (.r 2)
    rw [←map_inv,←map_mul,←map_mul,←map_mul]
    congr 1
  have hfix : ((u⁻¹*t*u : d.T) : G) ∈ centralizer (r.cover.borel.W₁ : Set G) := hk ▸ b.fixes
  have hm : (MulAut.conj (u : G)) ((u⁻¹*t*u : d.T) : G) ∈
      centralizer ((r.cover.borel.W₁.map (MulAut.conj (u : G)).toMonoidHom) : Set G) :=
    map_centralizer_le_centralizer_image _ _ (mem_map_of_mem _ hfix)
  rw [humap] at hm
  convert hm using 1
  change (t : G)=(u : G)*((u : G)⁻¹*(t : G)*(u : G))*(u : G)⁻¹
  group

/-- The selected graph involution fixes the actual component factor modulo R. -/
theorem source_selected_first_fixes_component_modulo {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r) :
    ∀ x ∈ componentPart d.Yplus L,
      (b.lift.dihedral.firstReflection : G)*x*(b.lift.dihedral.firstReflection : G)⁻¹*x⁻¹ ∈
        d.Y.pCoreIn 2 := by
  intro x hx
  exact source_cross_plane_commutator s h r
    (mem_sup_right b.lift.first_mem)
    (mem_sup_left (r.cover.plus ▸ ((map_subtype_le _).trans inf_le_left) hx))
    (source_selected_first_fixes_second s h r b) (r.cover.borel.component_centralizes hx)


/-- The selected Sylow maps bijectively to the actual residual quotient. -/
theorem source_sylow_quotient_bijective {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (X : Sylow 3 d.Y) :
    Function.Bijective ((QuotientGroup.mk' (pCore 2 d.Y)).comp (X : Subgroup d.Y).subtype) := by
  let q := QuotientGroup.mk' (pCore 2 d.Y)
  have hQ : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) :=
    IsPGroup.of_card (n:=2) (by simpa using r.cover.quotient_card)
  have hmap : (X : Subgroup d.Y).map q=⊤ :=
    (Sylow.is_maximal' (X.mapSurjective (QuotientGroup.mk'_surjective _))
      (hQ.to_subgroup ⊤) le_top).symm
  have hdis : Disjoint (X : Subgroup d.Y) (pCore 2 d.Y) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) _ _ X.isPGroup' pCore_isPGroup
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hdis x.property ((QuotientGroup.eq_one_iff _).mp hx)
  · intro y
    obtain ⟨x,hx,hxy⟩ := hmap.ge (mem_top y)
    exact ⟨⟨x,hx⟩,hxy⟩

/-- The actual selected Sylow has order nine. -/
theorem source_selected_sylow_card {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (b : SylowResult d I L r) :
    Nat.card ((b.lift.X : Subgroup d.Y).map d.Y.subtype)=9 := by
  rw [card_map_of_injective d.Y.subtype_injective]
  exact (Nat.card_congr (Equiv.ofBijective _ (source_sylow_quotient_bijective r b.lift.X))).trans
    r.cover.quotient_card

/-- Every element of the actual selected Sylow has cube one. -/
theorem source_selected_sylow_cube {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (r : LocalResult d I L)
    (b : SylowResult d I L r) {x : G}
    (hx : x ∈ (b.lift.X : Subgroup d.Y).map d.Y.subtype) : x^3=1 := by
  obtain ⟨x,hx,rfl⟩ := hx
  have he : Monoid.exponent (d.Y ⧸ pCore 2 d.Y) ∣3 := by
    rw [←r.cover.plus]
    exact s.earlier.quotient_exponent
  have hp : (⟨x,hx⟩ : b.lift.X)^3=1 := (source_sylow_quotient_bijective r b.lift.X).1 (by
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he _)
  exact congrArg (fun z : b.lift.X => ((z : d.Y) : G)) hp

/-- The residual Sylow cannot lie in the component, since the original cubic is outer. -/
theorem source_selected_sylow_not_component {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (b : SylowResult d I L r) :
    ¬ (b.lift.X : Subgroup d.Y).map d.Y.subtype ≤ L := by
  intro hPL
  let R := d.Y.pCoreIn 2
  have hcore : R.subgroupOf d.Y=pCore 2 d.Y :=
    comap_map_eq_self_of_injective d.Y.subtype_injective _
  let : (R.subgroupOf d.Y).Normal := by rw [hcore]; infer_instance
  have hQ : IsPGroup 3 (d.Y ⧸ R.subgroupOf d.Y) := by
    apply IsPGroup.of_card (n:=2)
    rw [hcore,r.cover.quotient_card]
    norm_num
  have hgen := SylowThreeNormalizer.sylow_supplement d.Y R (pCoreIn_le _ _) hQ b.lift.X
  have hYL : d.Y≤L := hgen ▸ sup_le hPL (r.cover.residual_core.le.trans inf_le_right)
  have hyY : (r.actor : G) ∈ d.Y := r.cover.plus ▸ r.actor.property
  have hyL := hYL hyY
  obtain ⟨_,a,ha,hreal⟩ := r.diagonal
  have hmarked := markedAction_eq_of_realizes r.marking (inclusion L.le_normalizer ⟨r.actor,hyL⟩) hreal
  apply ha
  rw [←hmarked,markedAction_on_component]
  exact ⟨_,rfl⟩

omit [Finite G] in
/-- The selected reflections normalize the actual residual Sylow. -/
theorem source_selected_normalizes {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (b : SylowResult d I L r) :
    (b.lift.dihedral.firstReflection : G) ∈ normalizer
      (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) ∧
    (b.lift.dihedral.halfTurn : G) ∈ normalizer
      (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) := by
  have hmem (x : DihedralGroup 4) :
      ((b.lift.dihedral.sectionMap x : d.T) : G) ∈ normalizer
        (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) :=
    ((b.lift.normalizer_T ▸ mem_map_of_mem (d.T : Subgroup G).subtype
      (show b.lift.dihedral.sectionMap x ∈ b.lift.dihedral.sectionMap.range from ⟨x,rfl⟩)) :
      ((b.lift.dihedral.sectionMap x : d.T) : G) ∈ (d.T : Subgroup G) ⊓ normalizer
        (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G)).2
  exact ⟨b.lift.dihedral.sectionMap_sr_zero ▸ hmem (.sr 0),
    b.lift.dihedral.sectionMap_r_two ▸ hmem (.r 2)⟩

/-- A nontrivial actual linear cubic is fixed by the selected graph involution. -/
theorem source_selected_fixed_component_cubic {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r) :
    ∃ x ∈ (b.lift.X : Subgroup d.Y).map d.Y.subtype,
      x ∈ componentPart d.Yplus L ∧ orderOf x=3 ∧
      (b.lift.dihedral.firstReflection : G)*x=x*(b.lift.dihedral.firstReflection : G) := by
  let A := componentPart d.Yplus L
  let P := (b.lift.X : Subgroup d.Y).map d.Y.subtype
  have hAY : A≤d.Y := r.cover.plus ▸ (map_subtype_le _).trans inf_le_left
  have hYA : d.Y≤normalizer (A : Set G) := by
    change d.Y≤normalizer (Stellmacher.twoResidualAmbient (d.Yplus⊓L) : Set G)
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    have hYY : d.Y≤normalizer (d.Yplus : Set G) := by rw [r.cover.plus]; exact d.Y.le_normalizer
    exact (le_normalizer_inf hYY (r.cover.plus.ge.trans r.cover.normalizes)).trans
      (normalizer_le_normalizer_characteristic_image (d.Yplus⊓L) (pResidual 2 _))
  have hd : 3∣Nat.card A := r.cover.borel.component_quotient ▸
    (pCore 2 A).card_quotient_dvd_card
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=A) 3 hd
  let zY : d.Y := ⟨z,hAY z.property⟩
  have hz3 : orderOf zY=3 := (Subgroup.orderOf_coe zY).symm.trans
    ((Subgroup.orderOf_coe z).trans hz)
  have hzP : IsPGroup 3 (zpowers zY) := IsPGroup.of_card (n:=1) (by
    rw [Nat.card_zpowers,hz3,pow_one])
  obtain ⟨X₀,hX₀⟩ := hzP.exists_le_sylow
  obtain ⟨y,hy⟩ := MulAction.exists_smul_eq d.Y X₀ b.lift.X
  let x : G := (y : G)*(z : G)*(y : G)⁻¹
  have hxP : x∈P := by
    change x ∈ (b.lift.X : Subgroup d.Y).map d.Y.subtype
    rw [←hy]
    exact mem_map_of_mem d.Y.subtype
      (mem_map_of_mem (MulAut.conj y).toMonoidHom (hX₀ (mem_zpowers zY)))
  have hxA : x∈A := (mem_normalizer_iff.mp (hYA y.property) z).mp z.property
  have hx3 : orderOf x=3 := (orderOf_injective (MulAut.conj (y : G)).toMonoidHom
    (MulAut.conj (y : G)).injective (z : G)).trans ((Subgroup.orderOf_coe z).trans hz)
  let tau : G := b.lift.dihedral.firstReflection
  have hcommR := source_selected_first_fixes_component_modulo s h r b x hxA
  have hcommP : tau*x*tau⁻¹*x⁻¹∈P := P.mul_mem
    ((mem_normalizer_iff.mp (source_selected_normalizes r b).1 x).mp hxP) (P.inv_mem hxP)
  have hdPR : Disjoint P (d.Y.pCoreIn 2) := IsPGroup.disjoint_of_ne 3 2 (by decide)
    _ _ (b.lift.X.isPGroup'.map d.Y.subtype) (isPGroup_pCoreIn 2 d.Y)
  have hzero : tau*x*tau⁻¹*x⁻¹=1 := disjoint_def.mp hdPR hcommP hcommR
  refine ⟨x,hxP,hxA,hx3,?_⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp hzero



/-- The actual common normalizer has order thirty-six and its cubic elements
are precisely the selected residual Sylow. -/
theorem source_selected_normalizer_cubics {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (r : LocalResult d I L)
    (b : SylowResult d I L r) :
    let P := (b.lift.X : Subgroup d.Y).map d.Y.subtype
    let N := (d.Y⊔d.S)⊓normalizer (P : Set G)
    Nat.card N=36 ∧ ∀ x : N, x^3=1 ↔ (x : G)∈P := by
  dsimp only
  let P := (b.lift.X : Subgroup d.Y).map d.Y.subtype
  let N := (d.Y⊔d.S)⊓normalizer (P : Set G)
  have hPN : P≤N := le_inf ((map_subtype_le _).trans le_sup_left) P.le_normalizer
  have hcard : Nat.card N=36 := by
    obtain ⟨e⟩ := b.lift.normalizer_YS
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hPcard : Nat.card (P.subgroupOf N)=9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv).trans (source_selected_sylow_card r b)
  let XN : Sylow 3 N := Sylow.ofCard (P.subgroupOf N) (by rw [hcard,hPcard]; decide +kernel)
  let : (P.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  let : XN.Normal := inferInstanceAs (P.subgroupOf N).Normal
  refine ⟨hcard,?_⟩
  intro x
  constructor
  · intro hx
    have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n:=1) (by
      rw [Nat.card_zpowers,pow_one]
      exact orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
    let := Sylow.unique_of_normal XN inferInstance
    have hQX : Q=XN := Subsingleton.elim _ _
    exact (hQX ▸ hQ) (mem_zpowers x)
  · intro hx
    exact Subtype.ext (source_selected_sylow_cube s r b hx)

/-- The selected field involution inverts every cubic element of the common normalizer. -/
theorem source_selected_field_inverts_cubics {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (r : LocalResult d I L)
    (b : SylowResult d I L r) :
    ∀ x ∈ (d.Y⊔d.S)⊓normalizer
      (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G), x^3=1 →
      (b.lift.dihedral.halfTurn : G)*x*(b.lift.dihedral.halfTurn : G)⁻¹=x⁻¹ := by
  intro x hx hx3
  have hxP := (source_selected_normalizer_cubics s r b).2 ⟨x,hx⟩ |>.mp (Subtype.ext hx3)
  obtain ⟨y,hy,hxy⟩ := hxP
  have he := b.lift.inverts (⟨y,hy⟩ : b.lift.X)
  change (y : G)=x at hxy
  simpa only [MulAut.conj_apply,hxy] using he

omit [Finite G] in
/-- The distinguished involutions are distinct and commute in the actual group. -/
theorem source_selected_pair_laws {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (b : SylowResult d I L r) :
    let tau : G := b.lift.dihedral.firstReflection
    let field : G := b.lift.dihedral.halfTurn
    tau^2=1 ∧ field^2=1 ∧ tau≠1 ∧ tau≠field ∧ tau*field=field*tau := by
  have ht : b.lift.dihedral.firstReflection^2=1 :=
    (orderOf_eq_prime_iff.mp b.lift.dihedral.firstReflection_order).1
  have hf : b.lift.dihedral.halfTurn^2=1 :=
    (orderOf_eq_prime_iff.mp b.lift.dihedral.halfTurn_order).1
  have ht1 : b.lift.dihedral.firstReflection≠1 := by
    intro he
    have hh := b.lift.dihedral.firstReflection_order
    rw [he,orderOf_one] at hh
    contradiction
  have htf : b.lift.dihedral.firstReflection≠b.lift.dihedral.halfTurn := by
    intro he
    have hh := congrArg b.lift.dihedral.projection he
    rw [b.lift.dihedral.projection_firstReflection,b.lift.dihedral.projection_halfTurn] at hh
    cases hh
  have hcomm : b.lift.dihedral.firstReflection*b.lift.dihedral.halfTurn=
      b.lift.dihedral.halfTurn*b.lift.dihedral.firstReflection := by
    rw [←b.lift.dihedral.sectionMap_sr_zero,←b.lift.dihedral.sectionMap_r_two,←map_mul,←map_mul]
    congr 1
  exact ⟨congrArg Subtype.val ht,congrArg Subtype.val hf,
    fun he => ht1 (Subtype.ext he),fun he => htf (Subtype.ext he),congrArg Subtype.val hcomm⟩

omit [Finite G] in
/-- None of the three selected involutions lies in the component. -/
theorem source_selected_pair_outside {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (r : LocalResult d I L) (b : SylowResult d I L r) :
    (b.lift.dihedral.firstReflection : G) ∉L ∧
    (b.lift.dihedral.halfTurn : G) ∉L ∧
    ((b.lift.dihedral.firstReflection : G)*(b.lift.dihedral.halfTurn : G)) ∉L := by
  have hker (t : d.T) : (t : G) ∈L ↔ b.lift.dihedral.projection t=1 := by
    change t ∈L.subgroupOf (d.T : Subgroup G) ↔ _
    exact Iff.symm (show t ∈ b.lift.dihedral.projection.ker ↔ t ∈ L.subgroupOf (d.T : Subgroup G) from
      Iff.of_eq (congrArg (fun K : Subgroup d.T => t∈K) b.lift.dihedral.kernel))
  refine ⟨?_,?_,?_⟩
  · rw [hker,b.lift.dihedral.projection_firstReflection]
    decide
  · rw [hker,b.lift.dihedral.projection_halfTurn]
    decide
  · change ((b.lift.dihedral.firstReflection*b.lift.dihedral.halfTurn : d.T) : G) ∉L
    rw [hker,map_mul,b.lift.dihedral.projection_firstReflection,b.lift.dihedral.projection_halfTurn]
    decide



open Matrix.PSL3Four.ExtendedCentralizer
open Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking

omit [Finite G] in
private theorem pair_fixed_cubic (x : SymmetricThree × SymmetricThree)
    (hx : x^3=1) (ht : (1,reflection)*x=x*(1,reflection)) :
    x=1 ∨ x=(rotation,1) ∨ x=(rotation^2,1) := by
  have hh : ∀ x : SymmetricThree × SymmetricThree,
      x^3=1 → (1,reflection)*x=x*(1,reflection) →
      x=1 ∨ x=(rotation,1) ∨ x=(rotation^2,1) := by decide +kernel
  exact hh x hx ht

/-- Any aligned symmetric-pair coordinates identify the actual component
intersection with the first cubic axis. -/
theorem source_selected_linear_axis {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r)
    (q : ((d.Y⊔d.S)⊓normalizer (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) : Subgroup G) ≃*
      (SymmetricThree × SymmetricThree))
    (tau field : ((d.Y⊔d.S)⊓normalizer (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G) : Subgroup G))
    (ht : (tau : G)=(b.lift.dihedral.firstReflection : G))
    (hf : (field : G)=(b.lift.dihedral.halfTurn : G))
    (hqt : q tau=(1,reflection)) (hqf : q field=(reflection,reflection)) :
    (L.subgroupOf ((d.Y⊔d.S)⊓normalizer
      (((b.lift.X : Subgroup d.Y).map d.Y.subtype) : Set G))).map q.toMonoidHom =
      (zpowers rotation).prod ⊥ := by
  let P := (b.lift.X : Subgroup d.Y).map d.Y.subtype
  let N := (d.Y⊔d.S)⊓normalizer (P : Set G)
  let K := (L.subgroupOf N).map q.toMonoidHom
  have hNL : N≤normalizer (L : Set G) := inf_le_left.trans
    ((by rw [←r.cover.plus]; exact h.outside.1.2 : d.Y⊔d.S≤I).trans
      (h.normalizes_component s.earlier))
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNL
  let : K.Normal := Subgroup.Normal.map inferInstance q.toMonoidHom q.surjective
  have hmem (x : N) : q x∈K ↔ (x : G)∈L := by
    change q x ∈ (L.subgroupOf N).map q.toMonoidHom ↔ _
    exact mem_map_iff_mem q.injective
  apply normal_eq_first_cubic K
  · rw [←hqt]
    exact fun hx => (source_selected_pair_outside r b).1 (ht ▸ (hmem tau).mp hx)
  · rw [←hqf]
    exact fun hx => (source_selected_pair_outside r b).2.1 (hf ▸ (hmem field).mp hx)
  · have he : q (tau*field)=(reflection,1) := by rw [map_mul,hqt,hqf]; decide +kernel
    rw [←he]
    intro hx
    apply (source_selected_pair_outside r b).2.2
    simpa only [Subgroup.coe_mul,ht,hf] using (hmem (tau*field)).mp hx
  · obtain ⟨x,hxP,hxA,hx3,hxt⟩ := source_selected_fixed_component_cubic s h r b
    have hxN : x∈N := ⟨mem_sup_left ((map_subtype_le _ ) hxP),P.le_normalizer hxP⟩
    let xN : N := ⟨x,hxN⟩
    have hx3N : xN^3=1 := Subtype.ext ((orderOf_eq_prime_iff.mp hx3).1)
    have hqx3 : (q xN)^3=1 := by rw [←map_pow,hx3N,map_one]
    have hqxt : (1,reflection)*q xN=q xN*(1,reflection) := by
      rw [←hqt,←map_mul,←map_mul]
      exact congrArg q (Subtype.ext (by
        change (tau : G)*x=x*(tau : G)
        rw [ht]
        exact hxt))
    have hxK : q xN∈K := (hmem xN).mpr ((map_subtype_le _ hxA).2)
    rcases pair_fixed_cubic (q xN) hqx3 hqxt with he | he | he
    · have hx1 : xN=1 := q.injective (he.trans (map_one q).symm)
      have hxG : x=1 := congrArg Subtype.val hx1
      rw [hxG,orderOf_one] at hx3
      contradiction
    · exact he ▸ hxK
    · have hh := K.pow_mem hxK 2
      rw [he] at hh
      have hp : ((rotation^2,1) : SymmetricThree × SymmetricThree)^2=(rotation,1) := by decide +kernel
      exact hp ▸ hh
  · intro hC
    apply source_selected_sylow_not_component r b
    intro x hxP
    have hxN : x∈N := ⟨mem_sup_left ((map_subtype_le _) hxP),P.le_normalizer hxP⟩
    let xN : N := ⟨x,hxN⟩
    apply (hmem xN).mp
    apply hC
    have h3 : (q xN)^3=1 := by
      rw [←map_pow,show xN^3=1 from Subtype.ext (source_selected_sylow_cube s r b hxP),map_one]
    have hc (z : SymmetricThree) (hz : z^3=1) : z∈zpowers rotation := by
      have hclass : ∀ y : SymmetricThree, y^3=1 → y=1 ∨ y=rotation ∨ y=rotation^2 := by decide +kernel
      rcases hclass z hz with rfl | rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
      · exact pow_mem (mem_zpowers _) _
    exact ⟨hc _ (congrArg Prod.fst h3),hc _ (congrArg Prod.snd h3)⟩



end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
