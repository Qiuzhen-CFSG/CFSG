module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar08

/-!
# Exact product checks on rows 512 through 575

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block08

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t512 tb512 ts512 _ _ ts512_sum ts512_parity
  apply product_cons_b t513 tb513 ts513 _ _ ts513_sum ts513_parity
  apply product_cons_b t514 tb514 ts514 _ _ ts514_sum ts514_parity
  apply product_cons_b t515 tb515 ts515 _ _ ts515_sum ts515_parity
  apply product_cons_b t516 tb516 ts516 _ _ ts516_sum ts516_parity
  apply product_cons_b t517 tb517 ts517 _ _ ts517_sum ts517_parity
  apply product_cons_b t518 tb518 ts518 _ _ ts518_sum ts518_parity
  apply product_cons_b t519 tb519 ts519 _ _ ts519_sum ts519_parity
  apply product_cons_b t520 tb520 ts520 _ _ ts520_sum ts520_parity
  apply product_cons_b t521 tb521 ts521 _ _ ts521_sum ts521_parity
  apply product_cons_b t522 tb522 ts522 _ _ ts522_sum ts522_parity
  apply product_cons_b t523 tb523 ts523 _ _ ts523_sum ts523_parity
  apply product_cons_b t524 tb524 ts524 _ _ ts524_sum ts524_parity
  apply product_cons_b t525 tb525 ts525 _ _ ts525_sum ts525_parity
  apply product_cons_b t526 tb526 ts526 _ _ ts526_sum ts526_parity
  apply product_cons_b t527 tb527 ts527 _ _ ts527_sum ts527_parity
  apply product_cons_b t528 tb528 ts528 _ _ ts528_sum ts528_parity
  apply product_cons_b t529 tb529 ts529 _ _ ts529_sum ts529_parity
  apply product_cons_b t530 tb530 ts530 _ _ ts530_sum ts530_parity
  apply product_cons_b t531 tb531 ts531 _ _ ts531_sum ts531_parity
  apply product_cons_b t532 tb532 ts532 _ _ ts532_sum ts532_parity
  apply product_cons_b t533 tb533 ts533 _ _ ts533_sum ts533_parity
  apply product_cons_b t534 tb534 ts534 _ _ ts534_sum ts534_parity
  apply product_cons_b t535 tb535 ts535 _ _ ts535_sum ts535_parity
  apply product_cons_b t536 tb536 ts536 _ _ ts536_sum ts536_parity
  apply product_cons_b t537 tb537 ts537 _ _ ts537_sum ts537_parity
  apply product_cons_b t538 tb538 ts538 _ _ ts538_sum ts538_parity
  apply product_cons_b t539 tb539 ts539 _ _ ts539_sum ts539_parity
  apply product_cons_b t540 tb540 ts540 _ _ ts540_sum ts540_parity
  apply product_cons_b t541 tb541 ts541 _ _ ts541_sum ts541_parity
  apply product_cons_b t542 tb542 ts542 _ _ ts542_sum ts542_parity
  apply product_cons_b t543 tb543 ts543 _ _ ts543_sum ts543_parity
  apply product_cons_b t544 tb544 ts544 _ _ ts544_sum ts544_parity
  apply product_cons_b t545 tb545 ts545 _ _ ts545_sum ts545_parity
  apply product_cons_b t546 tb546 ts546 _ _ ts546_sum ts546_parity
  apply product_cons_b t547 tb547 ts547 _ _ ts547_sum ts547_parity
  apply product_cons_b t548 tb548 ts548 _ _ ts548_sum ts548_parity
  apply product_cons_b t549 tb549 ts549 _ _ ts549_sum ts549_parity
  apply product_cons_b t550 tb550 ts550 _ _ ts550_sum ts550_parity
  apply product_cons_b t551 tb551 ts551 _ _ ts551_sum ts551_parity
  apply product_cons_b t552 tb552 ts552 _ _ ts552_sum ts552_parity
  apply product_cons_b t553 tb553 ts553 _ _ ts553_sum ts553_parity
  apply product_cons_b t554 tb554 ts554 _ _ ts554_sum ts554_parity
  apply product_cons_b t555 tb555 ts555 _ _ ts555_sum ts555_parity
  apply product_cons_b t556 tb556 ts556 _ _ ts556_sum ts556_parity
  apply product_cons_b t557 tb557 ts557 _ _ ts557_sum ts557_parity
  apply product_cons_b t558 tb558 ts558 _ _ ts558_sum ts558_parity
  apply product_cons_b t559 tb559 ts559 _ _ ts559_sum ts559_parity
  apply product_cons_b t560 tb560 ts560 _ _ ts560_sum ts560_parity
  apply product_cons_b t561 tb561 ts561 _ _ ts561_sum ts561_parity
  apply product_cons_b t562 tb562 ts562 _ _ ts562_sum ts562_parity
  apply product_cons_b t563 tb563 ts563 _ _ ts563_sum ts563_parity
  apply product_cons_b t564 tb564 ts564 _ _ ts564_sum ts564_parity
  apply product_cons_b t565 tb565 ts565 _ _ ts565_sum ts565_parity
  apply product_cons_b t566 tb566 ts566 _ _ ts566_sum ts566_parity
  apply product_cons_b t567 tb567 ts567 _ _ ts567_sum ts567_parity
  apply product_cons_b t568 tb568 ts568 _ _ ts568_sum ts568_parity
  apply product_cons_b t569 tb569 ts569 _ _ ts569_sum ts569_parity
  apply product_cons_b t570 tb570 ts570 _ _ ts570_sum ts570_parity
  apply product_cons_b t571 tb571 ts571 _ _ ts571_sum ts571_parity
  apply product_cons_b t572 tb572 ts572 _ _ ts572_sum ts572_parity
  apply product_cons_b t573 tb573 ts573 _ _ ts573_sum ts573_parity
  apply product_cons_b t574 tb574 ts574 _ _ ts574_sum ts574_parity
  apply product_cons_b t575 tb575 ts575 _ _ ts575_sum ts575_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d512 da512 ds512 _ _ ds512_sum ds512_parity
  apply product_cons_a d513 da513 ds513 _ _ ds513_sum ds513_parity
  apply product_cons_a d514 da514 ds514 _ _ ds514_sum ds514_parity
  apply product_cons_a d515 da515 ds515 _ _ ds515_sum ds515_parity
  apply product_cons_a d516 da516 ds516 _ _ ds516_sum ds516_parity
  apply product_cons_a d517 da517 ds517 _ _ ds517_sum ds517_parity
  apply product_cons_a d518 da518 ds518 _ _ ds518_sum ds518_parity
  apply product_cons_a d519 da519 ds519 _ _ ds519_sum ds519_parity
  apply product_cons_a d520 da520 ds520 _ _ ds520_sum ds520_parity
  apply product_cons_a d521 da521 ds521 _ _ ds521_sum ds521_parity
  apply product_cons_a d522 da522 ds522 _ _ ds522_sum ds522_parity
  apply product_cons_a d523 da523 ds523 _ _ ds523_sum ds523_parity
  apply product_cons_a d524 da524 ds524 _ _ ds524_sum ds524_parity
  apply product_cons_a d525 da525 ds525 _ _ ds525_sum ds525_parity
  apply product_cons_a d526 da526 ds526 _ _ ds526_sum ds526_parity
  apply product_cons_a d527 da527 ds527 _ _ ds527_sum ds527_parity
  apply product_cons_a d528 da528 ds528 _ _ ds528_sum ds528_parity
  apply product_cons_a d529 da529 ds529 _ _ ds529_sum ds529_parity
  apply product_cons_a d530 da530 ds530 _ _ ds530_sum ds530_parity
  apply product_cons_a d531 da531 ds531 _ _ ds531_sum ds531_parity
  apply product_cons_a d532 da532 ds532 _ _ ds532_sum ds532_parity
  apply product_cons_a d533 da533 ds533 _ _ ds533_sum ds533_parity
  apply product_cons_a d534 da534 ds534 _ _ ds534_sum ds534_parity
  apply product_cons_a d535 da535 ds535 _ _ ds535_sum ds535_parity
  apply product_cons_a d536 da536 ds536 _ _ ds536_sum ds536_parity
  apply product_cons_a d537 da537 ds537 _ _ ds537_sum ds537_parity
  apply product_cons_a d538 da538 ds538 _ _ ds538_sum ds538_parity
  apply product_cons_a d539 da539 ds539 _ _ ds539_sum ds539_parity
  apply product_cons_a d540 da540 ds540 _ _ ds540_sum ds540_parity
  apply product_cons_a d541 da541 ds541 _ _ ds541_sum ds541_parity
  apply product_cons_a d542 da542 ds542 _ _ ds542_sum ds542_parity
  apply product_cons_a d543 da543 ds543 _ _ ds543_sum ds543_parity
  apply product_cons_a d544 da544 ds544 _ _ ds544_sum ds544_parity
  apply product_cons_a d545 da545 ds545 _ _ ds545_sum ds545_parity
  apply product_cons_a d546 da546 ds546 _ _ ds546_sum ds546_parity
  apply product_cons_a d547 da547 ds547 _ _ ds547_sum ds547_parity
  apply product_cons_a d548 da548 ds548 _ _ ds548_sum ds548_parity
  apply product_cons_a d549 da549 ds549 _ _ ds549_sum ds549_parity
  apply product_cons_a d550 da550 ds550 _ _ ds550_sum ds550_parity
  apply product_cons_a d551 da551 ds551 _ _ ds551_sum ds551_parity
  apply product_cons_a d552 da552 ds552 _ _ ds552_sum ds552_parity
  apply product_cons_a d553 da553 ds553 _ _ ds553_sum ds553_parity
  apply product_cons_a d554 da554 ds554 _ _ ds554_sum ds554_parity
  apply product_cons_a d555 da555 ds555 _ _ ds555_sum ds555_parity
  apply product_cons_a d556 da556 ds556 _ _ ds556_sum ds556_parity
  apply product_cons_a d557 da557 ds557 _ _ ds557_sum ds557_parity
  apply product_cons_a d558 da558 ds558 _ _ ds558_sum ds558_parity
  apply product_cons_a d559 da559 ds559 _ _ ds559_sum ds559_parity
  apply product_cons_a d560 da560 ds560 _ _ ds560_sum ds560_parity
  apply product_cons_a d561 da561 ds561 _ _ ds561_sum ds561_parity
  apply product_cons_a d562 da562 ds562 _ _ ds562_sum ds562_parity
  apply product_cons_a d563 da563 ds563 _ _ ds563_sum ds563_parity
  apply product_cons_a d564 da564 ds564 _ _ ds564_sum ds564_parity
  apply product_cons_a d565 da565 ds565 _ _ ds565_sum ds565_parity
  apply product_cons_a d566 da566 ds566 _ _ ds566_sum ds566_parity
  apply product_cons_a d567 da567 ds567 _ _ ds567_sum ds567_parity
  apply product_cons_a d568 da568 ds568 _ _ ds568_sum ds568_parity
  apply product_cons_a d569 da569 ds569 _ _ ds569_sum ds569_parity
  apply product_cons_a d570 da570 ds570 _ _ ds570_sum ds570_parity
  apply product_cons_a d571 da571 ds571 _ _ ds571_sum ds571_parity
  apply product_cons_a d572 da572 ds572 _ _ ds572_sum ds572_parity
  apply product_cons_a d573 da573 ds573 _ _ ds573_sum ds573_parity
  apply product_cons_a d574 da574 ds574 _ _ ds574_sum ds574_parity
  apply product_cons_a d575 da575 ds575 _ _ ds575_sum ds575_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 512).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 512).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 512).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 512).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 512).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 512).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 512).take 64) RightCertificate.wideSecond ((tbRows.drop 512).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 512).take 64) RightCertificate.wideFirst ((daRows.drop 512).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block08
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
