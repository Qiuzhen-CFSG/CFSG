module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InsideOrthogonalCoordinatesSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.RootQuotientCoordinatesSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaCentralSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalFixedCommutator
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SingularGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedRootChoicesSource
/-!
# Fixed commutators in the actual full-cover block

For an involution of S outside R, the original core and root quotient admit
coherent orthogonal-cover coordinates. The fixed root quotient supplies a
nonidentity root lift, and supplies two distinct lifts unless q=4. Two fixed
roots generate the fixed root plane by commutators, so the fixed distinguished
center lies in C_R(a)′. In the q=4 case one fixed root gives a nonsingular
commutator outside the radical. The original distinguished center is radical,
and its outside conjugate is singular; hence this commutator belongs to the
literal distinguished set Δ.

All coordinates retain the original core inclusion and quotient maps. No
recognition of the full fixed block is required for this conclusion.

Source: Aschbacher–Smith, Lemma 2.4.12(2) and the full-cover inside case of
Lemma 2.4.21(2), printed pp.532 and 536.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem actual_fixed_core_mem
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (a : G) (b : MulAut (d.block.map d.H.subtype))
    (hbval : ∀l : d.block.map d.H.subtype, (b l : G)=a*(l:G)*a⁻¹)
    (u : pCore 2 (d.block.map d.H.subtype))
    (hu : MulAut.characteristic (pCore 2 (d.block.map d.H.subtype)) b u=u) :
    ((u : d.block.map d.H.subtype) : G)∈
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer ({a} : Set G) := by
  let L := d.block.map d.H.subtype
  have hcore : (pCore 2 L).map L.subtype=twoCore d.H :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
  refine ⟨(source_thompson_root_geometry d hG T hST hsingle hL hM hTM hunique).1
    (hcore.le (mem_map_of_mem L.subtype u.property)),?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have he := congrArg (fun v : pCore 2 L => ((v:L):G)) hu
  change (b u.val:G)=((u:L):G) at he
  rw [hbval] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem actual_root_coordinates
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    {b : MulAut (d.block.map d.H.subtype)}
    (k : ChapterC.OrthogonalInvolutionCoordinates (d.block.map d.H.subtype) n b) :
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    let hRL : R≤L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
    ∃ P : Sylow 2 (Representation.SL2OrthogonalCover.SL k.F), ∃ e : (R ⧸ N) ≃* P,
      ∀ r : R, (e (QuotientGroup.mk' N r) : Representation.SL2OrthogonalCover.SL k.F) =
        k.quotient (QuotientGroup.mk' (pCore 2 L) (inclusion hRL r)) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  obtain ⟨P,e,he⟩ := source_root_quotient_coordinates d hG T hST hsingle hL hM hTM hunique
  let P' := P.mapSurjective (f:=k.quotient.toMonoidHom) k.quotient.surjective
  let eP : P ≃* P' := equivMapOfInjective (P:Subgroup (L ⧸ pCore 2 L))
    k.quotient.toMonoidHom k.quotient.injective
  refine ⟨P',e.trans eP,?_⟩
  intro r
  change k.quotient (e (QuotientGroup.mk' N r))=_
  rw [he]

omit [Finite G] in
private theorem actual_fixed_root {L R : Subgroup G} (hRL : R≤L)
    (a : G) (b : MulAut L) (hbval : ∀l:L,(b l:G)=a*(l:G)*a⁻¹)
    (α : R→*R) (hαval : ∀r:R,(α r:G)=a*(r:G)*a⁻¹)
    (r : R) (hr : α r=r) :
    b (inclusion hRL r)=inclusion hRL r ∧
      (r:G)∈R⊓centralizer ({a}:Set G) := by
  have he : a*(r:G)*a⁻¹=(r:G) := (hαval r).symm.trans (congrArg Subtype.val hr)
  constructor
  · apply Subtype.ext
    exact (hbval (inclusion hRL r)).trans he
  · exact ⟨r.property,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm⟩

private theorem actual_fixed_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hz : center (d.block.map d.H.subtype)≠⊥)
    (a : G) (b : MulAut (d.block.map d.H.subtype))
    (hbval : ∀l : d.block.map d.H.subtype, (b l : G)=a*(l:G)*a⁻¹)
    (z : G) (hzZ : z∈distinguishedZ d⊓centralizer ({a}:Set G)) :
    ∃u:pCore 2 (d.block.map d.H.subtype),
      ((u:d.block.map d.H.subtype):G)=z ∧ (u:d.block.map d.H.subtype)∈center _ ∧
      MulAut.characteristic (pCore 2 (d.block.map d.H.subtype)) b u=u := by
  let L := d.block.map d.H.subtype
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcenter : center L≤pCore 2 L := by
    rw [source_block_core_eq_module d hG T hST hsingle]
    exact hK.center_le_module (source_block_core_eq_module d hG T hST hsingle)
  have hz' := hzZ.1
  rw [distinguishedZ_of_center_ne_bot d hz] at hz'
  obtain ⟨l,hl,hlz⟩ := hz'
  refine ⟨⟨l,hcenter hl⟩,hlz,hl,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (b l:G)=(l:G)
  change (l:G)=z at hlz
  rw [hbval,hlz,←mem_centralizer_singleton_iff.mp hzZ.2,mul_inv_cancel_right]

theorem source_noncenterless_inside_fixed_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype)≠⊥)
    (a : G) (haS : a∈(d.S:Subgroup d.H).map d.H.subtype) (ha2 : orderOf a=2)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    let I := R⊓centralizer ({a}:Set G)
    distinguishedZ d⊓centralizer ({a}:Set G)≤⁅I,I⁆ ∨
      (n=2 ∧ ∃u,u∈distinguishedDelta d x ∧ u∈⁅I,I⁆) := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  let I := R⊓centralizer ({a}:Set G)
  let hRL : R≤L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  let α := (R.normalizerMonoidHom ⟨a,source_field_actor_normalizes_thompson d a haS⟩).toMonoidHom
  have ha' : a^2=1 := by simpa only [ha2] using pow_orderOf_eq_one a
  obtain ⟨b,hb,hbval,ho,⟨k⟩⟩ := source_inside_orthogonal_involution_coordinates
    d hG T hST hsingle hL hM hTM hunique hz a haS ha' haR
  obtain ⟨P,e,he⟩ := actual_root_coordinates d hG T hST hsingle hL hM hTM hunique k
  obtain ⟨r,hrfix,hr1,ht⟩ := source_inside_fixed_root_choices
    d hG T hST hsingle hL hM hTM hunique c a haS ha' haR
  change α r=r at hrfix
  let g (r:R) := k.quotient (QuotientGroup.mk' (pCore 2 L) (inclusion hRL r))
  have hmem (r:R) : g r∈P := by
    change k.quotient (QuotientGroup.mk' (pCore 2 L) (inclusion hRL r))∈P
    rw [←he r]
    exact (e (QuotientGroup.mk' N r)).property
  have hne (r:R) (hr:QuotientGroup.mk' N r≠1) : g r≠1 := by
    intro hh
    have hh' : e (QuotientGroup.mk' N r)=1 := Subtype.ext ((he r).trans hh)
    exact hr (e.injective (hh'.trans e.map_one.symm))
  have hdata (r:R) (hr:α r=r) :
      b (inclusion hRL r)=inclusion hRL r ∧ (r:G)∈I :=
    actual_fixed_root hRL a b hbval α (fun _=>rfl) r hr
  have hfixed (u:pCore 2 L) (hu:MulAut.characteristic (pCore 2 L) b u=u) : ((u:L):G)∈I :=
    actual_fixed_core_mem d hG T hST hsingle hL hM hTM hunique a b hbval u hu
  rcases ht with hn | ⟨t,htfix,ht1,htr⟩
  · right
    refine ⟨hn,?_⟩
    obtain ⟨u,hufix,humoved,huform,hurad,huder⟩ :=
      k.exists_fixed_core_nonsingular_commutator I hfixed P (inclusion hRL r)
        (hdata r hrfix).2 (hdata r hrfix).1 (hmem r) (hne r hr1)
    refine ⟨((u:L):G),?_,huder⟩
    have hZR : ((u:L):G)∈R⊓centralizer (R:Set G) :=
      (source_thompson_root_geometry d hG T hST hsingle hL hM hTM hunique).2.2.1
        (commutator_mono (show I≤R from inf_le_left) (show I≤R from inf_le_left) huder)
    refine ⟨hZR,?_,?_⟩
    · intro huZ
      rw [distinguishedZ_of_center_ne_bot d hz] at huZ
      have huc : (u:L)∈center L := (mem_map_iff_mem L.subtype_injective).mp huZ
      exact hurad (k.center_mem_radical u huc)
    · intro huW
      exact huform (source_outside_center_singular d hG T hST hsingle hL hM hTM hunique
        c hz x hxT hxS k u huW)
  · left
    intro z hzZ
    obtain ⟨u,huz,huc,huf⟩ := actual_fixed_center d hG T hST hsingle hL hz a b hbval z hzZ
    have htr' : g r≠g t := by
      intro hgt
      have heq : e (QuotientGroup.mk' N t)=e (QuotientGroup.mk' N r) :=
        Subtype.ext ((he t).trans (hgt.symm.trans (he r).symm))
      exact htr (e.injective heq)
    have huP : (k.core u).toAdd∈Representation.OneCohomology.fixed
        ((Representation.SL2OrthogonalCover.action (F:=k.F)).comp P.toSubgroup.subtype) := by
      have hh := k.center_mem_radical u huc
      rw [←Representation.SL2OrthogonalCover.fixed_radical] at hh
      intro p
      exact hh p
    have hh := k.fixed_core_mem_commutator_of_two_roots I hfixed P
      (inclusion hRL r) (inclusion hRL t) (hdata r hrfix).2 (hdata t htfix).2
      (hdata r hrfix).1 (hdata t htfix).1 (hmem r) (hmem t) (hne r hr1) (hne t ht1)
      htr' u huf huP
    exact huz ▸ hh

end CFSG.Quasithin.Chapter2.LinearShadows.Single
