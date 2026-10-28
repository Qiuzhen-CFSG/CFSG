module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicBorels

/-!
# The derived lines and centers of the original large cubic cores

In the order243 branch of I.4(G1)–(G2), each original odd core D is
nonabelian, its derived subgroup is its original cubic line X, and its
center has order27. Consequently N_G(D)=N_G(X). The original local
extension S=D⟨y⟩ of order729 has an elementary center of order nine.

The outer involution fixes a plane of order nine in D. Involution fusion
and Sylow conjugacy inside H identify that plane with the original H-plane,
whose centralizer has order162. This excludes an abelian D. Brauer–Wielandt
then leaves center orders three or27. A center of order three makes S an
ambient Sylow with center X; the opposite core and the P×Q lemma would
force its Sylow center to be the nonconjugate opposite line, a contradiction.
Finally the opposite SL₂(3) action on Z(D) determines |Z(S)|=9. Its
ambient centralizer is odd: an involution would conjugate Z(S) to the
original plane, whose order162 centralizer cannot contain S. The original
four-group bounds that odd centralizer by729, so C_G(Z(S))=S. Thus
N_G(S)=N_G(Z(S)), retaining the literal ambient subgroups.

These are deductions from the original source configuration, not model
assumptions or a recognition theorem. They identify the actual cores and
normalizers needed to construct the compatible ternary completion. The
literal application is Chapter14MaximalStructure. Source: Aschbacher–Smith,
I.4(G1)–(G2) and I.4.5, printed p.417 (refs/quasithin.pdf, PDF p.428), using
the cubic centralizer splitting of Fong–Wong §3B, Nagoya Math. J.36 (1969),
p.156, and the P×Q lemma (Aschbacher–Smith A.1.18, printed p.24).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

private theorem nine_in_involution_centralizer_conjugate (t : CubicTorus c)
    (P : Subgroup G) (hP : Nat.card P=9) (u : G) (hu : orderOf u=2)
    (hPu : P≤Subgroup.centralizer ({u}:Set G)) :
    ∃ g : G, MulAut.conj g u=(t.z:G) ∧
      P.map (MulAut.conj g).toMonoidHom=
        zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
  obtain ⟨a,ha⟩ := isConj_iff.mp
    (involutions_conjugate c u t.z hu ((orderOf_coe t.z).trans t.z_order))
  let f := MulAut.conj a
  let R := P.map f.toMonoidHom
  let E := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hRH : R≤c.H := by
    rintro _ ⟨v,hv,rfl⟩
    rw [t.centralizer]
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (mem_centralizer_singleton_iff.mp (hPu hv))
    simp only [map_mul,show f u=(t.z:G) from ha] at hh
    exact hh
  have hR : Nat.card (R.subgroupOf c.H)=9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,
      card_map_of_injective f.injective,hP]
  have hEmap : E.map c.H.subtype=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hE : Nat.card E=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hEmap]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hi (A : Subgroup c.H) (hA : Nat.card A=9) : ¬3∣A.index := by
    have hh := A.card_mul_index
    rw [hA,H_card c] at hh
    have hh' : A.index=64 := by omega
    rw [hh']; decide
  let S : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hR).toSylow (hi _ hR)
  let T : Sylow 3 c.H := (IsPGroup.of_card (p:=3) (n:=2) hE).toSylow (hi _ hE)
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq c.H S T
  have hb' : (R.subgroupOf c.H).map (MulAut.conj b).toMonoidHom=E :=
    congrArg Sylow.toSubgroup hb
  refine ⟨(b:G)*a,?_,?_⟩
  · change (b:G)*a*u*((b:G)*a)⁻¹=(t.z:G)
    calc
      _ = (b:G)*(a*u*a⁻¹)*(b:G)⁻¹ := by group
      _ = (b:G)*(t.z:G)*(b:G)⁻¹ := by rw [ha]
      _ = (t.z:G) := by
        have hcomm : (b:G)*(t.z:G)=(t.z:G)*(b:G) :=
          mem_centralizer_singleton_iff.mp (t.centralizer ▸ b.property)
        rw [hcomm,mul_inv_cancel_right]
  · have hm := congrArg (fun A : Subgroup c.H => A.map c.H.subtype) hb'
    rw [hEmap] at hm
    rw [←hm]
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨b*⟨f w,hRH (mem_map_of_mem f.toMonoidHom hw)⟩*b⁻¹,
        mem_map_of_mem (MulAut.conj b).toMonoidHom
          (show (⟨f w,hRH (mem_map_of_mem f.toMonoidHom hw)⟩:c.H)∈R.subgroupOf c.H
            from mem_map_of_mem f.toMonoidHom hw),?_⟩
      change (b:G)*(a*w*a⁻¹)*(b:G)⁻¹=((b:G)*a)*w*((b:G)*a)⁻¹
      group
    · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
      obtain ⟨q,hq,hqv⟩ := (show (v:G)∈R from hv)
      refine ⟨q,hq,?_⟩
      change ((b:G)*a)*q*((b:G)*a)⁻¹=(b:G)*(v:G)*(b:G)⁻¹
      rw [←hqv]
      change ((b:G)*a)*q*((b:G)*a)⁻¹=(b:G)*(a*q*a⁻¹)*(b:G)⁻¹
      group

/-- The original outer involution fixes nine elements of the marked core. -/
theorem maximal_core_outer_fixed_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G) : Subgroup G)=9 := by
  have hh := cubic_oddCore_card_square c t.x t.x_order t.z t.n t.z_order t.n_order
    t.centralizer t.central_line t.outside t.invert_left
  rw [hc] at hh
  nlinarith

/-- An actual conjugation carries the fixed plane and involution to the original H markings. -/
theorem maximal_core_outer_fixed_conjugate (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ g : G, MulAut.conj g (t.n:G)=(t.z:G) ∧
      (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)).map
        (MulAut.conj g).toMonoidHom=
          zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) :=
  t.nine_in_involution_centralizer_conjugate _ (t.maximal_core_outer_fixed_card hc)
    t.n ((orderOf_coe t.n).trans t.n_order) inf_le_right

/-- The order243 core is nonabelian: otherwise it centralizes a plane with centralizer of order162. -/
theorem maximal_core_not_commutative (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ¬IsMulCommutative (cubicOddCore c t.x) := by
  intro he
  let D := cubicOddCore c t.x
  let F := D ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  let : IsMulCommutative D := he
  obtain ⟨g,_,hg⟩ := t.maximal_core_outer_fixed_conjugate hc
  have hd : D.map (MulAut.conj g).toMonoidHom≤Subgroup.centralizer (E:Set G) := by
    rintro _ ⟨d,hd,rfl⟩ v hv
    have hv' : v∈(cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)).map
        (MulAut.conj g).toMonoidHom := by rw [hg]; exact hv
    obtain ⟨w,hw,rfl⟩ := hv'
    have hcomm : w*d=d*w := congrArg Subtype.val (mul_comm' (⟨w,hw.1⟩:D) ⟨d,hd⟩)
    have hh := congrArg (MulAut.conj g) hcomm
    rw [map_mul,map_mul] at hh
    exact hh
  have hh := card_dvd_of_le hd
  rw [card_map_of_injective (MulAut.conj g).injective,hc,
    t.maximal_plane_centralizer_card hc] at hh
  norm_num at hh

/-- The derived subgroup is exactly the original marked cubic line. -/
theorem maximal_core_derived (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ⁅cubicOddCore c t.x,cubicOddCore c t.x⁆=zpowers ((t.x:c.H):G) := by
  have hle := (cubic_oddCore_inversion c t.x t.x_order t.z
    ((orderOf_coe t.z).trans t.z_order) t.centralizer).2
  have hd := card_dvd_of_le hle
  rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order] at hd
  have hne : Nat.card (⁅cubicOddCore c t.x,cubicOddCore c t.x⁆ : Subgroup G)≠1 := by
    intro h
    exact t.maximal_core_not_commutative hc
      (commutator_self_eq_bot_iff.mp (card_eq_one.mp h))
  have he := (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hne
  exact eq_of_le_of_card_ge hle (by
    rw [he,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order])

/-- The full normalizer of the core is its original cubic-line normalizer. -/
theorem maximal_core_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    normalizer (cubicOddCore c t.x:Set G)=cubicNormalizer c t.x := by
  apply le_antisymm
  · change normalizer (cubicOddCore c t.x:Set G)≤normalizer (zpowers ((t.x:c.H):G):Set G)
    rw [←t.maximal_core_derived hc,←map_subtype_commutator]
    exact normalizer_le_normalizer_characteristic_image _ (_root_.commutator _)
  · apply (normal_subgroupOf_iff_le_normalizer ?_).mp t.left_core_normal_in_cubic_normalizer
    rw [←t.maximal_cubic_normalizer_threeCore hc]
    exact pCoreIn_le 3 _


private theorem core_center_normalized (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x ≤ normalizer (centerIn (cubicOddCore c t.x):Set G) := by
  rw [←t.maximal_core_normalizer hc]
  exact normalizes_centerIn le_rfl

omit [Finite G] in
private theorem core_line_le_center (t : CubicTorus c) :
    zpowers ((t.x:c.H):G) ≤ centerIn (cubicOddCore c t.x) := by
  refine le_inf (cubic_line_le_oddCore c t.x t.x_order) ?_
  apply le_centralizer_iff.mp
  rw [zpowers_eq_closure,centralizer_closure]
  exact map_subtype_le _

private theorem maximal_center_orders (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (centerIn (cubicOddCore c t.x))=3 ∨
      Nat.card (centerIn (cubicOddCore c t.x))=27 := by
  let D := cubicOddCore c t.x
  let Z := centerIn D
  let X := zpowers ((t.x:c.H):G)
  let N := cubicNormalizer c t.x
  have hzn : (t.z:G)∈N := by
    dsimp only [N]
    rw [t.left_ambient_normalizer]
    exact mem_sup_right (mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers _)))
  have hnn : (t.n:G)∈N := by
    dsimp only [N]
    rw [t.left_ambient_normalizer]
    exact mem_sup_right (mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _)))
  let a : normalizer (Z:Set G) := ⟨t.z,t.core_center_normalized hc hzn⟩
  let b : normalizer (Z:Set G) := ⟨t.n,t.core_center_normalized hc hnn⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    rw [←Subgroup.coe_pow,show t.z^2=1 from t.z_order ▸ pow_orderOf_eq_one t.z]
    rfl)
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    rw [←Subgroup.coe_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n]
    rfl)
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hfixed : Z⊓Subgroup.centralizer ({(t.z:G)}:Set G)=X := by
    rw [←t.centralizer]
    apply le_antisymm
    · exact (inf_le_inf_right c.H (show Z≤D from inf_le_left)).trans
        (cubic_oddCore_fixed c t.x t.x_order).le
    · exact le_inf t.core_line_le_center (zpowers_le.mpr t.x.val.property)
  have hcommon : X⊓Subgroup.centralizer ({(t.n:G)}:Set G)=⊥ := by
    apply bot_unique
    intro v hv
    have hi := t.plane_inverted v (mem_sup_left hv.1)
    have hf : MulAut.conj (t.n:G) v=v := by
      change (t.n:G)*v*(t.n:G)⁻¹=v
      rw [←mem_centralizer_singleton_iff.mp hv.2,mul_inv_cancel_right]
    have h2 : v^2=1 := by
      have hinv : v=v⁻¹ := hf.symm.trans hi
      calc
        v^2 = v*v := pow_two v
        _ = v*v⁻¹ := congrArg (fun w => v*w) hinv
        _ = 1 := mul_inv_cancel v
    have h3 : v^3=1 := orderOf_dvd_iff_pow_eq_one.mp (by
      have hh := X.orderOf_dvd_natCard hv.1
      simpa only [X,Nat.card_zpowers,orderOf_coe,t.x_order] using hh)
    have he : v=1 := by
      simpa only [show 3=2+1 from rfl,pow_succ,h2,one_mul] using h3
    exact he
  have hodd : Odd (Nat.card Z) := (cubic_oddCore_odd c t.x).of_dvd_nat
    (card_dvd_of_le (show Z≤D from inf_le_left))
  have hformula := Z.card_three_odd_centralizers hodd a b ha hb hab
  change Nat.card Z * Nat.card
    ((Z⊓Subgroup.centralizer ({(t.z:G)}:Set G))⊓Subgroup.centralizer ({(t.n:G)}:Set G):Subgroup G)^2 =
    Nat.card (Z⊓Subgroup.centralizer ({(t.z:G)}:Set G):Subgroup G)*
    Nat.card (Z⊓Subgroup.centralizer ({(t.n:G)}:Set G):Subgroup G)*
    Nat.card (Z⊓Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G):Subgroup G) at hformula
  obtain ⟨q,hq,hqn⟩ := opposite_factor_swaps_torus_involutions c t.z t.n
    t.central_line t.n_order t.outside
  have hqN : (q:G)∈N := by
    dsimp only [N]
    rw [t.left_ambient_normalizer]
    exact mem_sup_left (mem_sup_right (mem_map_of_mem c.H.subtype hq))
  have hsame := Z.card_inf_centralizer_conj (q:G) (t.core_center_normalized hc hqN) (t.n:G)
  rw [show (q:G)*(t.n:G)*(q:G)⁻¹=(t.z:G)*(t.n:G) from congrArg Subtype.val hqn] at hsame
  rw [hfixed,hcommon,Subgroup.card_bot,one_pow,mul_one,←hsame,
    show Nat.card X=3 from by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]] at hformula
  have hd : Nat.card (Z⊓Subgroup.centralizer ({(t.n:G)}:Set G):Subgroup G)∣9 := by
    have hh := card_dvd_of_le (inf_le_inf_right (Subgroup.centralizer ({(t.n:G)}:Set G))
      (show Z≤D from inf_le_left))
    rwa [t.maximal_core_outer_fixed_card hc] at hh
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hd
  interval_cases k
  · rw [he] at hformula
    exact Or.inl (by norm_num at hformula; exact hformula)
  · rw [he] at hformula
    exact Or.inr (by norm_num at hformula; exact hformula)
  · have hZ : Nat.card Z=243 := by rw [he] at hformula; norm_num at hformula; exact hformula
    have hZD : Z=D := eq_of_le_of_card_ge inf_le_left (by rw [hZ,hc])
    apply False.elim
    apply t.maximal_core_not_commutative hc
    apply le_centralizer_iff_isMulCommutative.mp
    change D≤Subgroup.centralizer (D:Set G)
    exact hZD.ge.trans (show Z≤Subgroup.centralizer (D:Set G) from inf_le_right)

private theorem maximal_extension_of_center_line (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (hz : centerIn (cubicOddCore c t.x)=zpowers ((t.x:c.H):G)) :
    centerIn t.leftCoreExtension=zpowers ((t.x:c.H):G) ∧
      ∃ P : Sylow 3 G, (P:Subgroup G)=t.leftCoreExtension := by
  let D := cubicOddCore c t.x
  let X := zpowers ((t.x:c.H):G)
  let S := t.leftCoreExtension
  have hCD : Subgroup.centralizer (D:Set G)=X := by
    rw [t.left_oddCore_centralizer (by omega),←centerIn_eq_map_center,hz]
  have hXC : X≤Subgroup.centralizer (S:Set G) := by
    apply le_centralizer_iff.mp
    dsimp only [X]
    rw [zpowers_eq_closure,centralizer_closure]
    exact sup_le (map_subtype_le _)
      ((zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
        (opposite_factor_le_cubic_centralizer c t.x))
  have hXS : X≤S := t.core_line_le_center.trans (inf_le_left.trans le_sup_left)
  have hZS : centerIn S=X := le_antisymm
    (inf_le_right.trans ((centralizer_le (show D≤S from le_sup_left)).trans hCD.le))
    (le_inf hXS hXC)
  refine ⟨hZS,?_⟩
  have hSN : S≤cubicNormalizer c t.x :=
    (le_centralizer_iff.mp hXC).trans (Subgroup.centralizer_le_normalizer _)
  have hcontrol : normalizer (S:Set G)≤cubicNormalizer c t.x := by
    change normalizer (S:Set G)≤normalizer (X:Set G)
    rw [←hZS]
    exact normalizes_centerIn le_rfl
  have hi : ¬3∣S.relIndex (cubicNormalizer c t.x) := by
    have hh := relIndex_mul_relIndex (⊥:Subgroup G) S (cubicNormalizer c t.x) bot_le hSN
    simp only [relIndex_bot_left,S,t.maximal_leftCoreExtension_card hc,
      t.left_ambient_normalizer_card,hc] at hh
    change 729*S.relIndex (cubicNormalizer c t.x)=243*48 at hh
    have he : S.relIndex (cubicNormalizer c t.x)=16 := by omega
    rw [he]; decide
  have hp : IsPGroup 3 S := (t.maximal_leftCubicBorel_split hc).1
  have hg := not_dvd_relIndex_of_normalizer_inf_le S (cubicNormalizer c t.x) ⊤ hp le_top
    hi (inf_le_left.trans hcontrol)
  exact ⟨hp.toSylow (by simpa only [relIndex_top_right] using hg),rfl⟩

private theorem center_line_of_extension_center_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (hs : Nat.card (centerIn t.leftCoreExtension)=3) :
    centerIn (cubicOddCore c t.x)=zpowers ((t.x:c.H):G) := by
  let D := cubicOddCore c t.x
  let Z := centerIn D
  let X := zpowers ((t.x:c.H):G)
  let Y := zpowers ((t.y:c.H):G)
  let Q := zpowers (t.z:G)
  let S := t.leftCoreExtension
  let F := Z⊓Subgroup.centralizer (Y:Set G)
  have hFZ : F≤centerIn S := by
    refine le_inf (inf_le_left.trans (inf_le_left.trans le_sup_left)) ?_
    intro a ha s hs
    have hd : D≤Subgroup.centralizer ({a}:Set G) :=
      fun d hd => mem_centralizer_singleton_iff.mpr (ha.1.2 d hd)
    have hy : Y≤Subgroup.centralizer ({a}:Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (ha.2 y hy)
    exact mem_centralizer_singleton_iff.mp ((sup_le hd hy) hs)
  have hXF : X≤F := by
    refine le_inf t.core_line_le_center ?_
    apply le_centralizer_iff.mp
    dsimp only [X]
    rw [zpowers_eq_closure,centralizer_closure]
    exact (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (opposite_factor_le_cubic_centralizer c t.x)
  have hFX : X=F := eq_of_le_of_card_ge hXF (by
    have hh := card_le_of_le hFZ
    rw [hs] at hh
    simpa only [X,Nat.card_zpowers,orderOf_coe,t.x_order] using hh)
  have hYN : Y≤cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]
    exact (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (le_sup_right.trans le_sup_left)
  have hQN : Q≤cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]
    exact (zpowers_le.mpr (mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers t.z)))).trans
      le_sup_right
  have hCQ : Subgroup.centralizer (Q:Set G)=c.H := by
    dsimp only [Q]
    rw [zpowers_eq_closure,centralizer_closure,←t.centralizer]
  have hZp : IsPGroup 3 Z :=
    (t.left_oddCore_isThreeGroup.to_subgroup (Z.subgroupOf D)).of_equiv
      (subgroupOfEquivOfLe (show Z≤D from inf_le_left))
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (p:=3) (n:=1) (by
    rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order,pow_one])
  have hcop : Nat.Coprime 3 (Nat.card Q) := by
    rw [Nat.card_zpowers,orderOf_coe,t.z_order]; decide
  have hYQ : ⁅Y,Q⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
    rw [hCQ]; exact zpowers_le.mpr t.y.val.property)
  have hfix : Z⊓Subgroup.centralizer (Y:Set G)≤Subgroup.centralizer (Q:Set G) := by
    rw [hCQ]
    change F≤c.H
    rw [←hFX]
    exact zpowers_le.mpr t.x.val.property
  have hZQ := p_times_q_centralizer Y Q Z hYp hZp hcop
    (hYN.trans (t.core_center_normalized hc)) (hQN.trans (t.core_center_normalized hc)) hYQ hfix
  have hZH : Z≤c.H := hCQ ▸ commutator_eq_bot_iff_le_centralizer.mp hZQ
  exact le_antisymm ((le_inf (show Z≤D from inf_le_left) hZH).trans
    (cubic_oddCore_fixed c t.x t.x_order).le) t.core_line_le_center

/-- The original large core has center of order27, not order3. -/
theorem maximal_core_center_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (centerIn (cubicOddCore c t.x))=27 := by
  apply (t.maximal_center_orders hc).resolve_left
  intro hz
  have hline : centerIn (cubicOddCore c t.x)=zpowers ((t.x:c.H):G) :=
    (eq_of_le_of_card_ge t.core_line_le_center (by
      rw [hz,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order])).symm
  obtain ⟨hZP,P,hP⟩ := t.maximal_extension_of_center_line hc hline
  have hPc : Nat.card P=729 := by
    rw [hP,t.maximal_leftCoreExtension_card hc]
  have hPz : Nat.card (center P)=3 := by
    rw [←card_map_of_injective (P:Subgroup G).subtype_injective,←centerIn_eq_map_center,
      hP,hZP,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]
  have hy := t.oddCore_card_eq.symm.trans hc
  obtain ⟨Q,hSQ⟩ := (t.swap.maximal_leftCubicBorel_split hy).1.exists_le_sylow
  have hQc : Nat.card Q=729 := (Nat.card_congr (Q.equiv P).toEquiv).trans hPc
  have hSQeq : t.swap.leftCoreExtension=(Q:Subgroup G) := eq_of_le_of_card_ge hSQ (by
    rw [t.swap.maximal_leftCoreExtension_card hy]; exact hQc.le)
  have hSQz : Nat.card (centerIn t.swap.leftCoreExtension)=3 := by
    rw [hSQeq,centerIn_eq_map_center,card_map_of_injective (Q:Subgroup G).subtype_injective]
    exact (Nat.card_congr (centerCongr (Q.equiv P)).toEquiv).trans hPz
  have hlineY := t.swap.center_line_of_extension_center_card hy hSQz
  obtain ⟨hZQ,_,_⟩ := t.swap.maximal_extension_of_center_line hy hlineY
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have hmap : (P:Subgroup G).map (MulAut.conj g).toMonoidHom=(Q:Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  apply cubic_lines_not_conjugate c t.x t.y t.x_order g
  rw [←hZP,←hP,centerIn_map_equiv,hmap,←hSQeq,hZQ]
  rfl


/-- The local order729 subgroup has its center in the original core. -/
theorem maximal_extension_center (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    centerIn t.leftCoreExtension = centerIn (cubicOddCore c t.x) ⊓
      Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) := by
  let D := cubicOddCore c t.x
  let Y := zpowers ((t.y:c.H):G)
  let S := t.leftCoreExtension
  have hCD : Subgroup.centralizer (D:Set G)=centerIn D := by
    rw [t.left_oddCore_centralizer (by omega),centerIn_eq_map_center]
  apply le_antisymm
  · refine le_inf ?_ (inf_le_right.trans (centralizer_le (show Y≤S from le_sup_right)))
    exact inf_le_right.trans ((centralizer_le (show D≤S from le_sup_left)).trans hCD.le)
  · refine le_inf (inf_le_left.trans (inf_le_left.trans le_sup_left)) ?_
    intro a ha s hs
    have hd : D≤Subgroup.centralizer ({a}:Set G) :=
      fun d hd => mem_centralizer_singleton_iff.mpr (ha.1.2 d hd)
    have hy : Y≤Subgroup.centralizer ({a}:Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (ha.2 y hy)
    exact mem_centralizer_singleton_iff.mp ((sup_le hd hy) hs)

private theorem maximal_center_not_fixed_by_opposite (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ¬centerIn (cubicOddCore c t.x)≤
      Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G) := by
  intro hfix
  let D := cubicOddCore c t.x
  let Z := centerIn D
  let L := c.H₂
  have hLN : L.map c.H.subtype≤normalizer (Z:Set G) := by
    apply le_trans ?_ (t.core_center_normalized hc)
    rw [t.left_ambient_normalizer]
    exact le_sup_right.trans le_sup_left
  let j : L →* normalizer (Z:Set G) := {
    toFun l := ⟨((l:c.H):G),hLN (mem_map_of_mem c.H.subtype l.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let ρ : L →* MulAut Z := Z.normalizerMonoidHom.comp j
  have hy : t.y∈ρ.ker := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change ((t.y:c.H):G)*(v:G)*(((t.y:c.H):G))⁻¹=(v:G)
    have hcomm : (v:G)*((t.y:c.H):G)=((t.y:c.H):G)*(v:G) :=
      (hfix v.property _ (mem_zpowers _)).symm
    rw [←hcomm,mul_inv_cancel_right]
  have hd : 3∣Nat.card ρ.ker := by
    have hh := orderOf_dvd_natCard (⟨t.y,hy⟩:ρ.ker)
    rwa [orderOf_mk,t.y_order] at hh
  have hL : Nat.card L=24 := (Nat.card_congr c.H₂_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hi : ρ.ker.index∣8 := by
    have hh := ρ.ker.card_mul_index
    obtain ⟨k,hk⟩ := hd
    rw [hL,hk,mul_assoc] at hh
    have he : k*ρ.ker.index=8 := by omega
    exact ⟨k,by rw [mul_comm]; exact he.symm⟩
  have hp : IsPGroup 2 (L ⧸ ρ.ker) := IsPGroup.of_card_dvd_pow (p:=2) (n:=3) (by
    rw [←index_eq_card]; exact hi)
  have hperfect : IsPPerfect 2 L :=
    GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
      c.H₂_model.some.symm.toMonoidHom c.H₂_model.some.symm.surjective
  have htop := hperfect ρ.ker inferInstance hp
  let z : L := ⟨t.z,(t.central_line ▸ mem_zpowers t.z).2⟩
  have hz : ρ z=1 := by
    change z∈ρ.ker
    rw [htop]
    trivial
  have hZH : Z≤c.H := by
    intro v hv
    rw [t.centralizer]
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : MulAut Z => (a ⟨v,hv⟩:G)) hz
    change (t.z:G)*v*(t.z:G)⁻¹=v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hZX : Z≤zpowers ((t.x:c.H):G) :=
    (le_inf (show Z≤D from inf_le_left) hZH).trans
      (cubic_oddCore_fixed c t.x t.x_order).le
  have hh := card_le_of_le hZX
  rw [t.maximal_core_center_card hc,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order] at hh
  omega

/-- Its center is an elementary plane of order nine. -/
theorem maximal_extension_center_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (centerIn t.leftCoreExtension)=9 := by
  let D := cubicOddCore c t.x
  let X := zpowers ((t.x:c.H):G)
  let S := t.leftCoreExtension
  have hXD : X≤D := cubic_line_le_oddCore c t.x t.x_order
  have hXC : X≤Subgroup.centralizer (S:Set G) := by
    apply le_centralizer_iff.mp
    dsimp only [X]
    rw [zpowers_eq_closure,centralizer_closure]
    exact sup_le (map_subtype_le _)
      ((zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
        (opposite_factor_le_cubic_centralizer c t.x))
  have hXZ : X≤centerIn S := le_inf (hXD.trans le_sup_left) hXC
  have hdiv : Nat.card (centerIn S)∣27 := by
    have hle : centerIn S≤centerIn D := (t.maximal_extension_center hc).le.trans inf_le_left
    have hh := card_dvd_of_le hle
    rwa [t.maximal_core_center_card hc] at hh
  have hlo : 3≤Nat.card (centerIn S) := by
    have hh := card_le_of_le hXZ
    simpa only [X,Nat.card_zpowers,orderOf_coe,t.x_order] using hh
  have hne3 : Nat.card (centerIn S)≠3 := by
    intro h
    have he := t.center_line_of_extension_center_card hc h
    have hh := t.maximal_core_center_card hc
    rw [he,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order] at hh
    omega
  have hne27 : Nat.card (centerIn S)≠27 := by
    intro h
    have he : centerIn S=centerIn D := eq_of_le_of_card_ge
      ((t.maximal_extension_center hc).le.trans inf_le_left)
      (by rw [t.maximal_core_center_card hc,h])
    apply t.maximal_center_not_fixed_by_opposite hc
    exact he ▸ (t.maximal_extension_center hc).le.trans inf_le_right
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=3)).mp hdiv
  change Nat.card (centerIn S)=9
  interval_cases k <;> norm_num only [Nat.reducePow] at he
  · omega
  · exact (hne3 he).elim
  · exact he
  · exact (hne27 he).elim

/-- The center plane has exponent three with its original ambient placement. -/
theorem maximal_extension_center_elementary (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    IsElementaryAbelian 3 (centerIn t.leftCoreExtension) := by
  let Z := centerIn t.leftCoreExtension
  let : IsMulCommutative Z := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p:=3) (t.maximal_extension_center_card hc)
  refine {exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_}
  intro v
  have hv : (v:G)∈cubicOddCore c t.x :=
    (t.maximal_extension_center hc).le.trans (inf_le_left.trans inf_le_left) v.property
  apply Subtype.ext
  exact congrArg (fun a : cubicOddCore c t.x => (a:G)) (t.left_oddCore_cube ⟨v,hv⟩)

/-- The center plane of the local order729 subgroup has no involution in
its ambient centralizer. -/
theorem maximal_extension_center_centralizer_odd (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Odd (Nat.card (Subgroup.centralizer (centerIn t.leftCoreExtension:Set G))) := by
  let S := t.leftCoreExtension
  let K := centerIn S
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=Subgroup.centralizer (K:Set G)) 2
    (even_iff_two_dvd.mp heven)
  have hKv : K≤Subgroup.centralizer ({(v:G)}:Set G) :=
    fun k hk => mem_centralizer_singleton_iff.mpr (v.property k hk)
  obtain ⟨g,_,hg⟩ := t.nine_in_involution_centralizer_conjugate K
    (t.maximal_extension_center_card hc) v ((orderOf_coe v).trans hv) hKv
  have hS : S≤Subgroup.centralizer (K:Set G) :=
    le_centralizer_iff.mp (show K≤Subgroup.centralizer (S:Set G) from inf_le_right)
  have hmap : S.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer
      ((zpowers ((t.x:c.H):G)⊔zpowers ((t.y:c.H):G):Subgroup G):Set G) := by
    rintro _ ⟨a,ha,rfl⟩ b hb
    have hb' : b∈K.map (MulAut.conj g).toMonoidHom := hg.symm ▸ hb
    obtain ⟨k,hk,rfl⟩ := hb'
    have hh := congrArg (MulAut.conj g) (hS ha k hk)
    rw [map_mul,map_mul] at hh
    exact hh
  have hd := card_dvd_of_le hmap
  rw [card_map_of_injective (MulAut.conj g).injective,
    t.maximal_leftCoreExtension_card hc,t.maximal_plane_centralizer_card hc] at hd
  norm_num at hd

/-- The local order729 subgroup is the whole ambient centralizer of its
own center plane. -/
theorem maximal_extension_center_centralizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Subgroup.centralizer (centerIn t.leftCoreExtension:Set G)=t.leftCoreExtension := by
  let S := t.leftCoreExtension
  let K := centerIn S
  let C := Subgroup.centralizer (K:Set G)
  let A := t.torus.map c.H.subtype
  have hAN : A≤normalizer (C:Set G) :=
    ((normalizes_centerIn (t.maximal_leftCubicBorel_split hc).2.1).trans
      (normalizer_le_normalizer_centralizer K))
  have hzA : (t.z:G)∈A := mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers _))
  have hnA : (t.n:G)∈A := mem_map_of_mem c.H.subtype (mem_sup_right (mem_zpowers _))
  let a : normalizer (C:Set G) := ⟨t.z,hAN hzA⟩
  let b : normalizer (C:Set G) := ⟨t.n,hAN hnA⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hab2 : orderOf ((a*b:normalizer (C:Set G)):G)=2 := by
    apply orderOf_eq_prime
    · have hh := hab.mul_pow 2
      rw [ha,hb,one_mul] at hh
      exact congrArg Subtype.val hh
    · intro he
      have hni : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left
        (by simpa only [orderOf_coe,t.n_order,pow_two] using pow_orderOf_eq_one (t.n:G))
      have hzn : t.z=t.n := Subtype.ext ((eq_inv_of_mul_eq_one_left he).trans hni)
      exact t.outside (hzn ▸ mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1))
  have hodd : Odd (Nat.card C) := t.maximal_extension_center_centralizer_odd hc
  have hbound (v : G) (hv : orderOf v=2) :
      Nat.card (C⊓Subgroup.centralizer ({v}:Set G):Subgroup G)∣9 := by
    let F := C⊓Subgroup.centralizer ({v}:Set G)
    have ho : Odd (Nat.card F) := hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
    have hd : Nat.card F∣64*9 := by
      have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
      rwa [involution_centralizer_card c v hv] at hh
    exact (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd
  have hformula := C.card_three_odd_centralizers hodd a b ha hb hab
  have hd : Nat.card C∣
      Nat.card (C⊓Subgroup.centralizer ({(a:G)}:Set G):Subgroup G)*
      Nat.card (C⊓Subgroup.centralizer ({(b:G)}:Set G):Subgroup G)*
      Nat.card (C⊓Subgroup.centralizer ({((a*b:normalizer (C:Set G)):G)}:Set G):Subgroup G) := by
    rw [←hformula]
    exact dvd_mul_right _ _
  have hdiv : Nat.card C∣729 := hd.trans (Nat.mul_dvd_mul
    (Nat.mul_dvd_mul (hbound t.z ((orderOf_coe t.z).trans t.z_order))
      (hbound t.n ((orderOf_coe t.n).trans t.n_order)))
    (hbound ((a*b:normalizer (C:Set G)):G) hab2))
  have hSC : S≤C := le_centralizer_iff.mp
    (show K≤Subgroup.centralizer (S:Set G) from inf_le_right)
  exact (eq_of_le_of_card_ge hSC (by
    rw [t.maximal_leftCoreExtension_card hc]
    exact Nat.le_of_dvd (by decide) hdiv)).symm

/-- Normalizing the local order729 subgroup is equivalent to normalizing
its actual elementary center plane. -/
theorem maximal_extension_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    normalizer (t.leftCoreExtension:Set G)=normalizer (centerIn t.leftCoreExtension:Set G) := by
  apply le_antisymm (normalizes_centerIn le_rfl)
  conv_rhs => rw [←t.maximal_extension_center_centralizer hc]
  exact normalizer_le_normalizer_centralizer _

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
