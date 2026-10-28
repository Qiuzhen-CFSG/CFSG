module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialIntersection
public import Theory.Frattini.PGroupMap
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# A centralizing long-root pair for the actual G₂ special core

In the concrete root coordinates, the B and E long-root groups centralize
the C short-root involution. Their commutators fill the A highest-root
group. The pair lies in the special five-root radical, whose Frattini
subgroup is A, so the pair's join has Frattini subgroup exactly A.
The F-root element moves C modulo A, since its commutator with C is B.

Transport these calculations through both inverse maps of the original
compatible parabolic comparison. Agreement on the whole overlap makes
the two Weyl conjugations genuine ambient conjugations of the same root
center. The output retains the compatible map marking the C-root itself.
Solvable-residual and core transport identify that center with
Z(K), where K = O²(H), and put the pair in Q = O₂(K). Sylow uniqueness
in the model Borel identifies the inverse unipotent image with the original
S = O₂(N_G(L) ∩ H); hence the nonfixed-image witness belongs to that S.

The proved TI geometry makes the pair's join centralize any conjugate
root containing the selected involution. The existing intersection counts
and saturation then contradict fusion if both source placements hold:
S = Q C_{Q^g}(Z) would fix the involution modulo Z. The two centralizer
conjugations supplying those placements, transport of the selected short
root through them, and the triality pair remain to be proved. Original
uniqueness in Preparation and compatible comparison remain inputs;
exhaustive comparison, ambient recognition and GlobalExit are unfinished.
The Chapter12 companion applies the construction to the literal setup.

Source: Aschbacher–Smith F.4.35, printed p.292, and F.1.12(I)(3),
pp.262–264 (`refs/quasithin.pdf`). The coordinate formulas reuse the
existing licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace RootPair
variable {F : Type*} [Field F]

private def aRoot (a : F) : parabolic₁ (F := F) :=
  ⟨rootA a,radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel) (rootA_mem_radical₁ a)⟩
private def bRoot (a : F) : parabolic₁ (F := F) :=
  ⟨rootB a,radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel)
    ⟨![0,a,0,0,0,0],rfl,by simp [unipotentProduct]⟩⟩
private def cRoot (a : F) : parabolic₁ (F := F) :=
  ⟨rootC a,radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel)
    ⟨![0,0,a,0,0,0],rfl,by simp [unipotentProduct]⟩⟩
private def eRoot (a : F) : parabolic₁ (F := F) :=
  ⟨rootE a,radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel)
    ⟨![0,0,0,0,a,0],rfl,by simp [unipotentProduct]⟩⟩

private def aHom : Multiplicative F →* parabolic₁ (F := F) where
  toFun a := aRoot a.toAdd
  map_one' := Subtype.ext rootA_zero
  map_mul' a b := Subtype.ext (rootA_add a.toAdd b.toAdd).symm
private def bHom : Multiplicative F →* parabolic₁ (F := F) where
  toFun a := bRoot a.toAdd
  map_one' := Subtype.ext rootB_zero
  map_mul' a b := Subtype.ext (rootB_add a.toAdd b.toAdd).symm
private def eHom : Multiplicative F →* parabolic₁ (F := F) where
  toFun a := eRoot a.toAdd
  map_one' := Subtype.ext rootE_zero
  map_mul' a b := Subtype.ext (rootE_add a.toAdd b.toAdd).symm

private theorem bc_commute (a t : F) : Commute (bRoot a) (cRoot t) := by
  apply Subtype.ext
  change rootB a * rootC t = rootC t * rootB a
  have hB : rootB a = unipotentProduct ![0,a,0,0,0,0] := by simp [unipotentProduct]
  have hC : rootC t = unipotentProduct ![0,0,t,0,0,0] := by simp [unipotentProduct]
  rw [hB,hC,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters]

private theorem ec_commute (a t : F) : Commute (eRoot a) (cRoot t) := by
  apply Subtype.ext
  change rootE a * rootC t = rootC t * rootE a
  have hE : rootE a = unipotentProduct ![0,0,0,0,a,0] := by simp [unipotentProduct]
  have hC : rootC t = unipotentProduct ![0,0,t,0,0,0] := by simp [unipotentProduct]
  rw [hE,hC,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters]

private theorem be_commutator (a : F) : ⁅bRoot a,eRoot (1 : F)⁆=aRoot a := by
  apply Subtype.ext
  change ⁅rootB a,rootE (1:F)⁆ = rootA a
  have hh := fiveRoot_commutator (F := F)
    ![0,a,0,0,0,0] ![0,0,0,0,1,0] rfl rfl
  simpa [unipotentProduct] using hh

variable [Finite F] [CharP F 2]

private theorem pair_frattini {G : Type*} [Group G] [Finite G]
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f) :
    let U := (f.comp bHom).range ⊔ (f.comp eHom).range
    (frattini U).map U.subtype = (f.comp aHom).range := by
  let U := (f.comp bHom).range ⊔ (f.comp eHom).range
  let Q := (radical₁ (F := F)).subgroupOf parabolic₁
  have hBQ : bHom.range ≤ Q := by
    rintro _ ⟨a,rfl⟩
    exact ⟨![0,a.toAdd,0,0,0,0],rfl,by simp [bHom,bRoot,unipotentProduct]⟩
  have hEQ : eHom.range ≤ Q := by
    rintro _ ⟨a,rfl⟩
    exact ⟨![0,0,0,0,a.toAdd,0],rfl,by simp [eHom,eRoot,unipotentProduct]⟩
  have hUQ : U ≤ Q.map f := by
    apply sup_le <;> rw [MonoidHom.range_comp]
    exact map_mono hBQ
    exact map_mono hEQ
  have hpQ : IsPGroup 2 (Q.map f) := (radical₁_isTwoGroup.comap_subtype).map f
  let : Fact (IsPGroup 2 U) := ⟨hpQ.to_le hUQ⟩
  have hQQ : (frattini Q).map Q.subtype = aHom.range := by
    let eqv : Q ≃* radical₁ (F := F) := subgroupOfEquivOfLe
      (radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel))
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_map]
    have he : (parabolic₁ (F := F)).subtype.comp Q.subtype =
        (radical₁ (F := F)).subtype.comp eqv.toMonoidHom := rfl
    rw [he,←map_map,frattini_map_equiv,radical₁_frattini_eq_center,
      center_map_eq_highestRoot _ le_rfl (fiveRootSubgroup_le_unipotent _ _)]
    rw [←MonoidHom.range_comp]
    rfl
  apply le_antisymm
  · let : Fact (IsPGroup 2 (Q.map f)) := ⟨hpQ⟩
    have hmono := map_mono (f := (Q.map f).subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hUQ))
    let eqv := Q.equivMapOfInjective f hf
    have himage := frattini_map_equiv eqv
    rw [←himage,map_map,map_map] at hmono
    have hmap : (Q.map f).subtype.comp eqv.toMonoidHom = f.comp Q.subtype := rfl
    rw [hmap] at hmono
    change (frattini U).map U.subtype ≤ (frattini Q).map (f.comp Q.subtype) at hmono
    rw [←map_map,hQQ] at hmono
    simpa only [map_map, MonoidHom.range_comp] using hmono
  · rintro _ ⟨a,rfl⟩
    rw [show (f.comp aHom) a = ⁅f (bRoot a.toAdd),f (eRoot (1:F))⁆ by
      rw [←map_commutatorElement,be_commutator]; rfl]
    apply map_mono (commutator_le_frattini_of_isPGroup (p := 2))
    rw [map_subtype_commutator]
    exact commutator_mem_commutator (show f (bRoot a.toAdd) ∈ U from mem_sup_left ⟨a,rfl⟩)
      (show f (eRoot (1:F)) ∈ U from mem_sup_right ⟨Multiplicative.ofAdd (1:F),rfl⟩)

omit [Finite F] in
private theorem core_commutator {G : Type*} [Group G]
    (f : parabolic₁ (F := F) →* G) :
    let Q := ((radical₁ (F := F)).subgroupOf parabolic₁).map f
    ⁅Q,Q⁆ ≤ (f.comp aHom).range := by
  dsimp only
  rw [←map_commutator,MonoidHom.range_comp]
  apply map_mono
  apply (map_le_map_iff_of_injective (parabolic₁ (F := F)).subtype_injective).mp
  rw [map_commutator,map_subgroupOf_eq_of_le
    (radical₁_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel)),
    ←map_subtype_commutator,radical₁_commutator_eq_center,
    center_map_eq_highestRoot _ le_rfl (fiveRootSubgroup_le_unipotent _ _),
    ←MonoidHom.range_comp]
  exact le_rfl

private def fRoot : parabolic₁ (F := F) :=
  ⟨rootF 1,unipotent_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel)
    (subset_closure (by simp))⟩

omit [Finite F] in
private theorem fc_commutator (a : F) : ⁅(fRoot (F := F)),cRoot a⁆ = bRoot a := by
  apply Subtype.ext
  change ⁅rootF (1:F),rootC a⁆ = rootB a
  have hf : rootF (1 : F) = unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  have hc : rootC a = unipotentProduct ![0,0,a,0,0,0] := by simp [unipotentProduct]
  have hb : rootB a = unipotentProduct ![0,a,0,0,0,0] := by simp [unipotentProduct]
  rw [hf,hc,hb,commutatorElement_def,unipotentProduct_inv,unipotentProduct_inv,
    unipotentProduct_mul,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,
    CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod,CharTwo.add_self_eq_zero]

private theorem pair_transport {G : Type*} [Group G] [Finite G]
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (hagree : ∀ x : Model F, ∀ h₁ : x ∈ parabolic₁, ∀ h₂ : x ∈ parabolic₂,
      f ⟨x,h₁⟩ = l ⟨x,h₂⟩) (t : F) (ht : t ≠ 0) :
    let Z := (f.comp aHom).range
    let Q := ((radical₁ (F := F)).subgroupOf parabolic₁).map f
    ∃ v ∈ Q, v = f (cRoot t) ∧ v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ ((unipotent (K := F)).subgroupOf parabolic₁).map f, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z := by
  let r := l ⟨weylR,weylR_mem_parabolic⟩
  let w : parabolic₁ (F := F) := ⟨weylS,mem_sup_right (subset_closure (by simp))⟩
  let s := f w * r
  have hconjB (a : F) : r * f (aRoot a) * r⁻¹ = f (bRoot a) := by
    have hA₂ : rootA a ∈ parabolic₂ (F := F) :=
      unipotent_le_local₂.trans (le_sup_left.trans_eq local₂_sup_borel) (subset_closure (by simp))
    have hB₂ : rootB a ∈ parabolic₂ (F := F) :=
      unipotent_le_local₂.trans (le_sup_left.trans_eq local₂_sup_borel) (subset_closure (by simp))
    rw [hagree _ (aRoot a).property hA₂,hagree _ (bRoot a).property hB₂]
    change l _ * l _ * (l _)⁻¹ = l _
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
    exact Subtype.ext (weylR_rootA a)
  have hconjE (a : F) : s * f (aRoot a) * s⁻¹ = f (eRoot a) := by
    calc
      _ = f w * (r * f (aRoot a) * r⁻¹) * (f w)⁻¹ := by dsimp [s]; group
      _ = f w * f (bRoot a) * (f w)⁻¹ := by rw [hconjB]
      _ = f (w * bRoot a * w⁻¹) := by simp only [map_mul,map_inv]
      _ = f (eRoot a) := congrArg f (Subtype.ext (weylS_rootB a))
  have hB : ((f.comp aHom).range).map (MulAut.conj r).toMonoidHom = (f.comp bHom).range := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(hconjB a.toAdd).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨_,⟨a,rfl⟩,hconjB a.toAdd⟩
  have hE : ((f.comp aHom).range).map (MulAut.conj s).toMonoidHom = (f.comp eHom).range := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(hconjE a.toAdd).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨_,⟨a,rfl⟩,hconjE a.toAdd⟩
  refine ⟨f (cRoot t),mem_map_of_mem _ ?_,rfl,?_,?_,?_,r,s,?_⟩
  · exact ⟨![0,0,t,0,0,0],rfl,by simp [cRoot,unipotentProduct]⟩
  · rintro ⟨a,ha⟩
    have he : rootA a.toAdd = rootC t := congrArg Subtype.val (hf ha)
    have hp : unipotentProduct ![a.toAdd,0,0,0,0,0] = unipotentProduct ![0,0,t,0,0,0] := by
      simpa [unipotentProduct] using he
    have hh := congrFun (unipotentProduct_injective hp) 2
    exact ht (by simpa using hh.symm)
  · apply orderOf_eq_prime_iff.mpr
    refine ⟨?_,?_⟩
    · rw [←map_pow]
      have hs : (cRoot t)^2=1 := Subtype.ext (by
        change rootC t * rootC t = 1
        rw [rootC_add,CharTwo.add_self_eq_zero,rootC_zero])
      rw [hs,map_one]
    · intro he
      have hh : rootC t = rootC 0 := by
        simpa only [cRoot,rootC_zero,Subgroup.coe_one] using congrArg Subtype.val
          (hf (he.trans (map_one f).symm))
      exact ht (rootC_injective hh)
  · refine ⟨f fRoot,mem_map_of_mem _ (show fRoot ∈ (unipotent (K := F)).subgroupOf parabolic₁ from
      subset_closure (by simp [fRoot])),?_⟩
    rw [←map_commutatorElement,fc_commutator]
    rintro ⟨a,ha⟩
    have hh : rootA a.toAdd = rootB t := congrArg Subtype.val (hf ha)
    have hcoords : unipotentProduct ![a.toAdd,0,0,0,0,0] = unipotentProduct ![0,t,0,0,0,0] := by
      simpa [unipotentProduct] using hh
    exact ht (by simpa using (congrFun (unipotentProduct_injective hcoords) 1).symm)
  · dsimp only
    rw [hB,hE]
    refine ⟨sup_le ?_ ?_,sup_le ?_ ?_,pair_frattini f hf⟩
    · rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem f (show bHom a ∈ (radical₁ (F := F)).subgroupOf parabolic₁ from
        ⟨![0,a.toAdd,0,0,0,0],rfl,by simp [bHom,bRoot,unipotentProduct]⟩)
    · rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem f (show eHom a ∈ (radical₁ (F := F)).subgroupOf parabolic₁ from
        ⟨![0,0,0,0,a.toAdd,0],rfl,by simp [eHom,eRoot,unipotentProduct]⟩)
    · rintro _ ⟨a,rfl⟩
      exact mem_centralizer_singleton_iff.mpr ((bc_commute a.toAdd t).map f).eq
    · rintro _ ⟨a,rfl⟩
      exact mem_centralizer_singleton_iff.mpr ((ec_commute a.toAdd t).map f).eq

omit [Finite F] in
private theorem local_center :
    (center (local₁ (F := F))).map local₁.subtype = highestRoot := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    have hLP : local₁ (F := F) ≤ parabolic₁ := le_sup_left.trans_eq local₁_sup_borel
    have hc : (⟨a.val,hLP a.property⟩ : parabolic₁ (F := F)) ∈
        centralizer ((radical₁ (F := F)).subgroupOf parabolic₁ : Set (parabolic₁ (F := F))) := by
      apply mem_centralizer_iff.mpr
      intro r hr
      apply Subtype.ext
      change (r.val : Model F) * a.val = a.val * r.val
      exact congrArg (fun k : local₁ (F := F) => k.val)
        (mem_center_iff.mp ha ⟨r.val,radical₁_le_local₁ hr⟩)
    have har : a.val ∈ radical₁ (F := F) := EvenLocal.short_radical_selfCentralizing hc
    rw [←center_map_eq_highestRoot (radical₁ (F := F)) le_rfl
      (fiveRootSubgroup_le_unipotent _ _)]
    refine ⟨⟨a.val,har⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
    apply Subtype.ext
    change (r.val : Model F) * a.val = a.val * r.val
    exact congrArg (fun k : local₁ (F := F) => k.val)
      (mem_center_iff.mp ha ⟨r.val,radical₁_le_local₁ r.property⟩)
  · rintro _ ⟨a,rfl⟩
    refine ⟨⟨rootA a.toAdd,radical₁_le_local₁ (rootA_mem_radical₁ _)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (local₁_le_centralizer_rootA a.toAdd x.property))

private theorem saturation_fixes_point_mod_center
    {G : Type*} [Group G] {K S : Subgroup G} {v : G}
    (hv : v ∈ K.pCoreIn 2) (hc : ⁅K.pCoreIn 2,K.pCoreIn 2⁆ ≤ (center K).map K.subtype)
    (hn : S ≤ normalizer (K.pCoreIn 2 : Set G))
    (g : G) (hvg : v ∈ ((center K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (hS : S = K.pCoreIn 2 ⊔ ((K.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center K).map K.subtype : Subgroup G) : Set G))) :
    ∀ x ∈ S, ⁅x,v⁆ ∈ (center K).map K.subtype := by
  let Q := K.pCoreIn 2
  let R := Q.map (MulAut.conj g).toMonoidHom ⊓
    centralizer (((center K).map K.subtype : Subgroup G) : Set G)
  have hRN : R ≤ normalizer (Q : Set G) := (le_sup_right.trans hS.ge).trans hn
  have hRV : R ≤ centralizer ({v} : Set G) := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    obtain ⟨z,⟨k,hk,rfl⟩,he⟩ := hvg
    apply mem_centralizer_singleton_iff.mpr
    rw [←he,←map_mul,←map_mul]
    exact congrArg (MulAut.conj g).toMonoidHom (congrArg (fun t : K => t.val)
      (mem_center_iff.mp hk ⟨y,map_subtype_le _ hy⟩))
  intro x hx
  have hx' : x ∈ (Q : Set G) * (R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R hRN]
    exact hS ▸ hx
  obtain ⟨q,hq,r,hr,rfl⟩ := hx'
  have he : ⁅r,v⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hRV hr))
  rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
  exact hc (commutator_mem_commutator hq hv)

end RootPair
variable {G : Type*} [Group G] [Finite G]

/-- The actual G₂ right core contains a short-root involution centralized
by two ambient conjugates of its root center. Their join has precisely that
root center as its Frattini subgroup. The conjugators use both compatible
parabolic maps, including their agreement on the whole overlap. The same
involution has a nonfixed image under the original S. TI gives whole-root
centralization, and the source counts exclude simultaneous Sylow placements
under fusion. The compatible map marks the selected C-root explicitly. -/
theorem Preparation.g2_special_core_root_pair
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val = v ∧ (e.right w).val = rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ sourceS L H, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        U ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        Z ≤ Q.map (MulAut.conj g).toMonoidHom →
        ¬ Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) ≤ sourceS L H) := by
  have hcompare := he
  have hTI := d.g2_right_center_fusion h hH hp F he
  have hF := (d.g2_local_structure h hH.1.1.2 hp F he).1
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hH.1.1.2 hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := P₀.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have ha (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂) :
      f ⟨x,hx⟩ = l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    have hright := congrArg Subtype.val (e.symm.right_commutes b)
    have hleft := congrArg Subtype.val (e.symm.left_commutes b)
    exact hright.trans hleft.symm
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J = solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f = residual H := by
    rw [hJ,show f = P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hCJ : (center J).map J.subtype = RootPair.aHom.range := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroup_center_eq _ (parabolic₁ (F := F)).subtype_injective,
      map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),RootPair.local_center,
      ←MonoidHom.range_comp]
    rfl
  have hZ : (f.comp RootPair.aHom).range =
      (center (residual H)).map (residual H).subtype := by
    rw [MonoidHom.range_comp,←hCJ,map_subgroup_center_eq f hf,hJf]
  have hQ : ((radical₁ (F := F)).subgroupOf parabolic₁).map f = (residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 local₁ parabolic₁
      (le_sup_left.trans_eq local₁_sup_borel),local₁_pCore] at hh
    exact hh
  have hS : ((unipotent (K := F)).subgroupOf parabolic₁).map f = sourceS L H := by
    let a : P →* Model F := (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom
    let V := ((sourceS L H).subgroupOf P).map a
    have hVP : IsPGroup 2 V := ((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map a
    have hVB : V ≤ Atlas.G2.borel := by
      rintro _ ⟨x,hx,rfl⟩
      let b : (P₀ ⊓ P : Subgroup G) := ⟨x.val,((show sourceS L H ≤ P₀ from le_sup_right.trans le_sup_left) hx),x.property⟩
      have heq := congrArg Subtype.val (e.right_commutes b)
      change a x = (e.middle b).val at heq
      rw [heq]
      exact (ChapterF.GreenBook.LieModels.G2.overlap_eq_borel (F := F)).le (e.middle b).property
    let U := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
      (show unipotent ≤ Atlas.G2.borel from le_sup_left)
    let : (U : Subgroup (Atlas.G2.borel (K := F))).Normal := EvenBorelTorus.radical_normal
    let := Sylow.unique_of_normal U (inferInstance : U.Normal)
    obtain ⟨D,hD⟩ := (hVP.comap_subtype : IsPGroup 2 (V.subgroupOf Atlas.G2.borel)).exists_le_sylow
    have hDU : D = U := Subsingleton.elim _ _
    have hVU : V ≤ unipotent := by
      intro x hx
      have hh := hD (show (⟨x,hVB hx⟩ : Atlas.G2.borel (K := F)) ∈ V.subgroupOf Atlas.G2.borel from hx)
      rw [hDU] at hh
      exact hh
    obtain ⟨D,hD⟩ := (d.hypothesisF11 h hH.1.1.2).sylow_parabolic 1
    let U' := ((unipotent (K := F)).subgroupOf parabolic₁).map e.right.symm.toMonoidHom
    have hSU : (D : Subgroup P) ≤ U' := by
      intro x hx
      have hxS : x.val ∈ sourceS L H := hD.le (mem_map_of_mem P.subtype hx)
      have hxU : a x ∈ unipotent := hVU (mem_map_of_mem a hxS)
      exact ⟨e.right x,hxU,e.right.symm_apply_apply x⟩
    have heq := D.is_maximal' ((unipotent_isTwoGroup.comap_subtype).map e.right.symm.toMonoidHom) hSU
    change ((unipotent (K := F)).subgroupOf parabolic₁).map (P.subtype.comp e.right.symm.toMonoidHom) = _
    rw [←map_map]
    change U'.map P.subtype = _
    change U' = (D : Subgroup P) at heq
    rw [heq]
    exact hD
  have hh := RootPair.pair_transport f hf l ha (1:F) one_ne_zero
  dsimp only at hh ⊢
  rw [hZ,hQ,hS] at hh
  obtain ⟨v,hv,hvmark,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat⟩ := hh
  refine ⟨e,v,hv,?_,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat,?_,?_⟩
  · refine ⟨e.right.symm (RootPair.cRoot (1:F)),hvmark.symm,?_⟩
    exact congrArg Subtype.val (e.right.apply_symm_apply (RootPair.cRoot (1:F)))
  · intro g hvg
    let := hTI.1
    have hv1 : v ≠ 1 := by intro heq; simp [heq] at hv2
    exact center_conjugate_pair hTI.2.1 g r s v hvg hv1
      (le_sup_left.trans hUC) (le_sup_right.trans hUC)
  · intro g hvg hZQ hRS
    have hg : g ∉ normalizer (residual H : Set G) := by
      intro hg
      have hh := mem_normalizer_iff_map_conj_eq.mp (hTI.2.2.symm ▸ hg)
      exact hvz (hh ▸ hvg)
    have hs := (d.g2_special_core_saturation h hH hp F hcompare g hg hZQ hRS).2
    have hclass := RootPair.core_commutator f
    dsimp only at hclass
    rw [hQ,hZ] at hclass
    have hnQ : sourceS L H ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
      d.S_normalizes_right.trans (normalizer_le_normalizer_characteristic_image
        (residual H) (pCore 2 (residual H)))
    obtain ⟨x,hx,hxv⟩ := hmoved
    exact hxv (RootPair.saturation_fixes_point_mod_center hv hclass hnQ g hvg hs x hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
