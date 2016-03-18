package jacquesb.cvm;

import java.io.PipedWriter;
import java.io.PipedReader;
import java.io.IOException;
import java.io.BufferedReader;

import android.app.Activity;
import android.os.Bundle;
import android.widget.Button;
import android.widget.EditText;
import android.widget.LinearLayout;
import android.widget.TextView;
import android.widget.Toast;
import android.view.View;
import android.view.View.OnClickListener;
import android.content.Context;
import android.os.Handler;
import android.util.Log;

import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;

public class cvm extends Activity
{
    private EditText et;
    cvmview myview;

    /** Called when the activity is first created. */
    @Override
    public void onCreate(Bundle savedInstanceState)
    {
        super.onCreate(savedInstanceState);
        // setContentView(R.layout.main);

        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
        		LinearLayout.LayoutParams.FILL_PARENT, 
        		LinearLayout.LayoutParams.WRAP_CONTENT);
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        
        /* Create a TextView and set its content.
         * the text is retrieved by calling a native
         * function.
         */
        TextView  tv = new TextView(this);
        tv.setText( "CVM" );
        layout.addView(tv);
        
        et = new EditText(this);
        et.setText ("");
        et.setLayoutParams(params);
        layout.addView(et);
        
        Button btn = new Button(this);
        btn.setText("OK");
        btn.setLayoutParams(params);
        btn.setOnClickListener(btnListener);
        layout.addView(btn);

	myview = new cvmview(this);
	layout.addView(myview);
        
        LinearLayout.LayoutParams layoutParam =
        	new LinearLayout.LayoutParams(
        			LinearLayout.LayoutParams.FILL_PARENT,
        			LinearLayout.LayoutParams.WRAP_CONTENT);
        
        this.addContentView(layout, layoutParam);

        init();
        
    }

    private OnClickListener btnListener = new OnClickListener ()
    {
    	public void onClick (View v)
    	{
		String input = et.getText().toString();
		String output = jni (input);
    		// Toast.makeText(getBaseContext(), "Clicked:("+input+")->"+output+".", Toast.LENGTH_LONG).show();
		et.setText(output);

		myview.invalidate();
    	}
    };

    private int trace (String s)
    {
	// Toast.makeText(getBaseContext(), s, Toast.LENGTH_LONG).show();
	Log.d ("cvmlog", s);
	return 0;
    }

    private void invalidate_view ()
    {
	trace ("java invalidate");
	myview.invalidate();
    }

    private class cvmview extends View 
    {
	public cvmview (Context context)
        {
	    super(context);
	}
	@Override protected void onDraw (Canvas canvas)
	{
	    int i, x, y, r;
	    super.onDraw(canvas);
	    Paint paint = new Paint();
	    paint.setStyle(Paint.Style.FILL);
	    paint.setColor(Color.BLACK);
	    canvas.drawPaint(paint);
	    paint.setColor(Color.GREEN);
	    canvas.drawCircle (20, 20, 15, paint);
	    /*
	    paint.setColor(0xFF123456);
	    canvas.drawCircle (50, 40, 10, paint);
	    */
            /* jnidraw (canvas, paint); */

	    int n = getdrawnbr();
	    trace ("getdrawnbr->"+Integer.toString(n));
            for (i=0; i<n; i++)
	    {
		trace ("i="+Integer.toString(i));
		int op = getdrawop(i);
		trace ("op="+Integer.toString(op));
		int c = getdrawcolor(i);
		trace ("color="+Integer.toString(c));
		paint.setColor(c);
		switch (op)
		{
		    case 1:
			x = getdrawparam(i,0);
			y = getdrawparam(i,1);
			canvas.drawPoint (x, y, paint);
			break;
		    case 2:
			canvas.drawPaint (paint);
			break;
		    case 3:
			trace ("circle");
			x = getdrawparam(i,0);
			y = getdrawparam(i,1);
			r = getdrawparam(i,2);
			trace ("x="+Integer.toString(x)+" y="+Integer.toString(y)+" r="+Integer.toString(r));
			canvas.drawCircle (x, y, r, paint);
			break;
		    default:
			break;
		}
	    }
	    
	}
    }

    public native int init ();
    public native String jni (String input);
    public native int jnidraw (Canvas canvas, Paint paint);
    public native int getdrawnbr ();
    public native int getdrawop (int i);
    public native int getdrawcolor (int i);
    public native int getdrawparam (int i, int j);

    static {
        System.loadLibrary("cvm");
    }

}
